{-# LANGUAGE RecordWildCards #-}
module Data.Foop.Eval (new, run, Entity(..), type Tell, type Request, tell, request) where

{-- need to not export run --}

import Control.Monad.Free.Church ( foldF, retract ) 
import qualified Control.Monad.Trans.State as ST
import Control.Monad.Trans.Class ( MonadTrans(lift) ) 
import Control.Monad.Reader ( MonadIO(..) ) 
import Data.Kind ( Type, Constraint ) 
import Control.Comonad.Store
    ( Comonad(extract), store, ComonadStore(seeks), Store ) 
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

type MkStorage ::  Row SlotData -> Row Type 
type family MkStorage rt where 
  MkStorage (R lts) = MkStorage_ lts 

type MkStorage_ :: [LT (Type,Type -> Type,Type -> Type)] -> Row Type  
type family MkStorage_ lts where 
  MkStorage_ '[] = Empty 
  MkStorage_ (l :-> '(i,q,m) ': lts) = Extend l (M.Map i (Entity m q)) (MkStorage_ lts)

type StorageConstraint :: Row SlotData -> Constraint 
type family StorageConstraint slots where 
  StorageConstraint slots =  ( Forall slots SlotOrdC 
                             , Forall (MkStorage slots) Default
                             , WellBehaved slots
                             , WellBehaved (MkStorage slots)) 

mkStorage :: forall slots
           . StorageConstraint slots 
          => Proxy slots  -> Rec (MkStorage slots)
mkStorage proxy = R.default' @Default def

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, and a Context which can be read from inside the Prototype monad 
data EvalState slots cxt st q m 
  = EvalState {
      _entity  :: Spec slots cxt st q m 
    , _state   :: st 
    , _context :: cxt 
    , _storage :: Rec (MkStorage slots)
  }

data ExEvalState :: (Type -> Type) -> (Type -> Type) -> Type where 
  ExEvalState :: EvalState ev cxt st q  m 
              -> ExEvalState q m 

withExEval :: forall q m r  
            . ExEvalState q m 
            -> (forall ev cxt st. EvalState ev cxt st q m -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

new :: forall slots cxt q m 
        . (MonadIO m, StorageConstraint slots)
       => Prototype slots cxt q  m 
       -> cxt 
       -> m (Entity m q ) 
new (Prototype espec@(MkSpec{..})) c  = liftIO (newTVarIO e') >>= \e -> pure $ Entity e 
  where 
    evalSt = initE espec c 

    e' = mkEntity_ evalSt 

initE :: StorageConstraint slots 
      => Spec slots cxt st q m 
      -> cxt 
      -> EvalState slots cxt st q m 
initE espec@MkSpec {..} cxt  
  = EvalState {_entity = espec 
              ,_state = initialState 
              ,_context =  cxt 
              ,_storage = mkStorage slots}  

newtype Transformer q m = Transformer {transform :: forall x. q x -> m (x,ExEvalState q m)}

type EntityStore q  m      = Store (ExEvalState q  m) (Transformer q m)

-- This is quite different from Halogen (which is the basis for the foundation of all the Prototype stuff) so, quick explanation: 
-- EntityS is a TVar that holds a store comonad which spits out a *function* from the input to m newEvalState
-- This is kind of a weird construction but because StateT isn't a comonad and we need a StateT from which we can *extract* the state at any time
-- (for queries), -- it serves its purpose
newtype Entity m q = Entity {entity :: TVar (EntityStore q m)}

mkEntity_ :: forall ev cxt st q m
           . Monad m =>  EvalState ev cxt st q  m -> EntityStore q  m 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState q m -> Transformer q m
    go ex@(ExEvalState es@EvalState {..}) = Transformer $ \qx -> do  
      let (EntityM ai) = apNT (queryHandler _entity) (Q . liftCoyoneda $ qx)
      let  st          = foldF (evalF es) ai
      ST.runStateT st ex

-- | Given an input type for some entity and the entity, run it, returning (maybe) some output 
run :: forall x m q. MonadIO m => q x -> Entity m q -> m x
run i (Entity tv) = do
  e <- liftIO $ readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  liftIO . atomically . writeTVar tv $ newObj -- write new store thingy to tvar 
  pure x 

type Tell q = () -> q ()

tell :: forall m q. MonadIO m => Tell q -> Entity m q -> m ()
tell q = run (q ())

tellAll :: forall m q t. (Traversable t, MonadIO m) => Tell q -> t (Entity m q) -> m ()
tellAll q es = mapM_ (tell q) es  

type Request q a = (a -> a) -> q a 

request :: forall m q x. MonadIO m => Request q x -> Entity m q -> m x 
request q = run (q id) 

requestAll :: forall m q t x. (Traversable t, MonadIO m) => Request q x -> t (Entity m q) -> m (t x) 
requestAll q es = mapM (request q) es 

evalF :: forall ev' cxt' st' q'  m' a' 
    .  Monad m' 
    => EvalState ev' cxt' st' q'  m'
    -> EntityF ev' cxt' st' q' m' a'
    -> ST.StateT (ExEvalState q' m') m' a' 
evalF EvalState {..} = \case 
  State f -> case f _state of 
    (a,newState) -> do 
        ST.modify $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Ask f   -> pure (f _context)

  Query q -> case apNT (queryHandler _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  








