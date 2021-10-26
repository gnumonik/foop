{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Eval (new, run, Entity(..), type Tell, type Request, mkTell, mkRequest) where

{-- need to not export run --}

import Control.Monad.Free.Church ( foldF, retract ) 
import qualified Control.Monad.Trans.State as ST
import Control.Monad.Trans.Class ( MonadTrans(lift) ) 
import Control.Monad.Reader ( MonadIO(..) ) 
import Data.Kind ( Type, Constraint ) 
import Control.Comonad.Store
    ( Comonad(extract), store, ComonadStore(seeks, peek, pos), Store ) 
import Control.Concurrent.STM
    ( atomically, newTVarIO, readTVarIO, writeTVar, TVar )
import Data.Foop.Entity
    ( apNT, AlgebraQ(Q), Prototype(..), Spec(..), SlotOrdC )
import Data.Foop.EntityF ( EntityF(..), EntityM(EntityM), SlotData ) 
import Data.Functor.Coyoneda
import Data.Row 
import Data.Row.Internal
import qualified Data.Map.Strict as M
import qualified Data.Row.Records as R 
import Data.Default 
import Data.Proxy (Proxy(..))
import Data.Singletons.TypeLits (Symbol)
import qualified Control.Monad.State.Class as S 

-- storage stuff, has to be here for staging reasons; the type family that 
-- creates the storage type from the `slots` field of a Spec requires the 
-- "Entity" type to be in scope

type ChildStorage :: Row SlotData -> Type 
type ChildStorage slots = Rec (MkStorage slots)

type MkStorage ::  Row SlotData -> Row Type 
type family MkStorage rt where 
  MkStorage (R lts) = MkStorage_ lts 

type MkStorage_ :: [LT (Type,Type,Type -> Type,Type -> Type)] -> Row Type  
type family MkStorage_ lts where 
  MkStorage_ '[] = Empty 
  MkStorage_ (l :-> '(r,i,q,m) ': lts) = Extend l (M.Map i (Entity r m q)) (MkStorage_ lts)


type ChildC :: Symbol -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Row SlotData -> Constraint 
type family ChildC childLabel index rendered q m slots where 
  ChildC lbl i r q m slots = (HasType lbl (M.Map i (Entity r m q)) (MkStorage slots)
                             ,HasType lbl (M.Map i r) (MkRenderTree slots)
                             ,SlotConstraint slots
                             ,KnownSymbol lbl)

type StorageConstraint :: Row SlotData -> Constraint 
type family StorageConstraint slots where 
  StorageConstraint slots =  ( Forall slots SlotOrdC 
                             , Forall (MkStorage slots) Default
                             , WellBehaved slots
                             , WellBehaved (MkStorage slots)) 

type RenderConstraint :: Row SlotData -> Constraint 
type family RenderConstraint slots where 
  RenderConstraint slots = (Forall slots SlotOrdC 
                           ,Forall (MkRenderTree slots) Default 
                           ,WellBehaved slots 
                           ,WellBehaved (MkRenderTree slots))

type MkRenderTree :: Row SlotData -> Row Type 
type family MkRenderTree slots where 
  MkRenderTree (R lts) = MkRenderTree_ lts 

type MkRenderTree_ :: [LT (Type,Type,Type -> Type,Type -> Type)] -> Row Type 
type family MkRenderTree_ slots where
  MkRenderTree_ '[] = Empty 
  MkRenderTree_ (l :-> '(r,i,q,m) ': lts) = Extend l (M.Map i r) (MkRenderTree_ lts)

type SlotConstraint slots = (StorageConstraint slots, RenderConstraint slots)

mkStorage :: forall slots
           . StorageConstraint slots 
          => Proxy slots  -> Rec (MkStorage slots)
mkStorage proxy = R.default' @Default def

mkRenderTree :: forall slots 
              . SlotConstraint slots 
            => Proxy slots -> Rec (MkRenderTree slots)
mkRenderTree proxy = R.default' @Default def 

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: Row SlotData -> Type -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type
data EvalState slots rendered cxt st q m 
  = EvalState {
      _entity     :: Spec slots rendered cxt st q m 
    , _state      :: st 
    , _context    :: cxt 
    , _storage    :: Rec (MkStorage slots)
    , _renderTree :: Rec (MkRenderTree slots)
  }

data ExEvalState :: Type -> (Type -> Type) -> (Type -> Type) -> Type where 
  ExEvalState :: EvalState slots rendered cxt st q  m 
              -> ExEvalState rendered q m 

withExEval :: forall q m rendered  r
            . ExEvalState rendered q m 
            -> (forall slots cxt st. EvalState slots rendered cxt st q m -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

new :: forall slots cxt q m r
        . (MonadIO m, SlotConstraint slots)
       => Prototype slots r cxt q  m 
       -> cxt 
       -> m (Entity r m q ) 
new (Prototype espec@MkSpec{..}) c  = liftIO (newTVarIO e') >>= \e -> pure $ Entity e 
  where 
    evalSt = initE espec c 

    e' = mkEntity_ evalSt 

initE :: SlotConstraint slots 
      => Spec slots r cxt st q m 
      -> cxt 
      -> EvalState slots r cxt st q m 
initE espec@MkSpec {..} cxt  
  = EvalState {_entity     = espec 
              ,_state      = initialState 
              ,_context    =  cxt 
              ,_storage    = mkStorage slots
              ,_renderTree = mkRenderTree slots}  

newtype Transformer r q m = Transformer {transform :: forall x. q x -> m (x,ExEvalState r q m)}

type EntityStore r q  m = Store (ExEvalState r q  m) (Transformer r q m)

-- This is quite different from Halogen (which is the basis for all the Prototype stuff) so, quick explanation: 
-- EntityS is a TVar that holds a store comonad which spits out a *function* from the input to m newEvalState
-- This is kind of a weird construction but because StateT isn't a comonad and we need a StateT from which we can *extract* the state at any time
-- (for queries)
newtype Entity r m q = Entity {entity :: TVar (EntityStore r q m)}

mkEntity_ :: forall slots r cxt st q m
           . Monad m =>  EvalState slots r cxt st q  m -> EntityStore r q m 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState r q m -> Transformer r q m
    go ex@(ExEvalState es@EvalState {..}) = Transformer $ \qx -> do  
      let (EntityM ai) = apNT (handleQuery _entity) (Q . liftCoyoneda $ qx)
      let  st          = foldF (evalF es) ai
      ST.runStateT st ex

-- | Given an input type for some entity and the entity, run it, returning (maybe) some output 
run :: forall x m q r. MonadIO m => q x -> Entity r m q -> m x
run i (Entity tv) = do
  e <- liftIO $ readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  liftIO . atomically . writeTVar tv $ newObj -- write new store thingy to tvar 
  pure x 

type Tell q = () -> q ()

mkTell :: Tell q -> q ()
mkTell q  = q ()


tell :: forall lbl i r q m slots state context
      . ChildC lbl i r q m slots 
     => i 
     -> Tell q 
     -> EntityM slots context state q m ()
tell i q = do 
  storage <- gets _

--tellAll :: forall m q t r. (Traversable t, MonadIO m) => Tell q -> t (Entity r m q) -> m ()
--tellAll q es = mapM_ (mkTell q) es  


type Request q a = (a -> a) -> q a 

mkRequest :: Request q x -> q x
mkRequest q = q id 

renderE :: MonadIO m => Entity r m q -> m r 
renderE (Entity tv) = do 
  e <- liftIO $ readTVarIO tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> pure $ render _entity _state 
  


--requestAll :: forall r m q t x. (Traversable t, MonadIO m) => Request q x -> t (Entity r m q) -> m (t x) 
--requestAll q es = mapM (mkRequest q) es 

evalF :: forall slots' r' cxt' st' q'  m' a' 
    .  Monad m' 
    => EvalState slots' r' cxt' st' q'  m'
    -> EntityF slots' cxt' st' q' m' a'
    -> ST.StateT (ExEvalState r' q' m') m' a' 
evalF EvalState {..} = \case 
  State f -> case f _state of 
    (a,newState) -> do 
        ST.modify $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Ask f   -> pure (f _context)

  Query q -> case apNT (handleQuery _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  










