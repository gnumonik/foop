{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Foop.EntityF ( EntityM(..)
                         , EntityF(..)
                         , MonadLook(..)
                         , type SlotData) where

import Control.Monad.Free.Church ( liftF, F(..), foldF ) 
import Control.Monad.State.Class ( MonadState(state) ) 
import Control.Monad.Trans.Class ( MonadTrans(..) ) 
import Control.Monad.Reader ( MonadIO(..), MonadTrans(..) ) 
import Control.Monad.IO.Class ( MonadIO(..) ) 
import Data.Kind ( Type, Constraint ) 
import Data.Bifunctor ( Bifunctor(first) ) 
import Data.Functor.Coyoneda ( Coyoneda, liftCoyoneda )
import Data.Row 
import Data.Constraint 
import Data.Functor.Coyoneda ( Coyoneda(..) )
import Data.Functor (($>))
import Data.Row.Records hiding (transform)
import GHC.TypeLits (Symbol)
import Data.Singletons hiding (type (~>))
import Data.Row 
import Data.Row.Internal
import qualified Data.Map.Strict as M
import qualified Data.Row.Records as R 
import Data.Default 
import Data.Proxy (Proxy(..))
import Data.Singletons.TypeLits (Symbol)
import qualified Control.Monad.State.Class as S 
import Control.Comonad.Store
import Control.Concurrent.STM
import qualified Control.Monad.State as ST



------ EntityF.hs

type SlotData = (Type,Type, Type -> Type, Type -> Type)

class Monad m => MonadLook l m where 
  look :: m l 

data Slot :: Symbol -> Row SlotData -> (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where 
  Slot :: ( HasType l (M.Map i (Entity r m q)) (MkStorage slots)
          , HasType l (M.Map i r) (MkRenderTree slots)
          , KnownSymbol l 
          , Ord i
          , MonadIO m) => Slot l slots q m i r

slotLabel :: forall slots q m i r l. Slot l slots q m i r -> Label l 
slotLabel Slot = Label @l

type EntityF :: Row SlotData -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
data EntityF slots context state query m a where 
  State  :: (state -> (a,state)) -> EntityF slots context state query m a

  Lift   :: m a -> EntityF slots context state query m a

  Ask    :: (context -> a) -> EntityF slots context state query m a

  Query  :: Coyoneda query a -> EntityF slots context state query m a

  Child  :: Slot l slots q n i r -> (M.Map i (Entity r n q) -> a) -> EntityF slots context state query m a 

  Surface:: Slot l slots q n i r -> (M.Map i r -> a) -> EntityF slots context state query m a 

  Create :: Slot l slots q n i r -> i -> Entity r n q -> a -> EntityF slots context state query m a 

  Delete :: Slot l slots q n i r -> i -> a -> EntityF slots context state query m a 


instance Functor m => Functor (EntityF slots i state query m) where
  fmap f = \case 
    State k          -> State (first f . k)
    Lift ma          -> Lift (f <$> ma)
    Ask r            -> Ask $ fmap f r
    Query qb         -> Query $ fmap f qb 
    Child key g      -> Child key $ fmap f g 
    Surface key g    -> Surface key $ fmap f g  
    Create key i e a -> Create key i e (f a)
    Delete key i a   -> Delete key i (f a) 


newtype EntityM slots i state query  m a = EntityM (F (EntityF slots i state query m) a) deriving (Functor, Applicative, Monad)  

instance Functor m => MonadState s (EntityM slots r s q m) where 
  state f = EntityM . liftF . State $ f 

instance MonadIO m => MonadIO (EntityM slots r s q m) where 
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM slots r s q ) where 
  lift = EntityM . liftF . Lift 

instance Functor m => MonadLook l (EntityM slots l s q m) where 
  look = EntityM . liftF . Ask $ id 

----- Entity.hs 

type SlotOrdC :: (Type, Type, Type -> Type, Type -> Type) -> Constraint 
class SlotOrdC slot where 
instance Ord i => SlotOrdC '(r,i,q,m) 

data Prototype :: Row SlotData -> Type -> Type ->  (Type -> Type) -> (Type -> Type) -> Type where 
  Prototype :: Forall slots SlotOrdC 
            => Spec slots rendered context state query m 
            -> Prototype slots rendered context query m

type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

newtype AlgebraQ query a =  Q (Coyoneda query a) 

{--

It seems like we have 2 options for 'render': 

  1) Parameterize the monad over some "render output" type and automatically construct a 
     "tree" (in practice it'd probably be a Row of...something). This is hard but doable. 

  2) Make the render function be of type `state -> IO ()`. This is easy and convenient but 
     it introduces IO in a weird place. 

So 1) seems preferable. In order to implement it, we'd have to add a type var parameter to 
the spec (but not the EntityF/M, I think) which would have to be visible in the spec and 
the EvalSpec. I'm not sure if we can existentialize it away in the ExEvalSpec but it's not a 
huge deal if we can't, just makes things a bit more complicated

The real problem is: How the fuck do we construct and manipulate the "tree"? And how do we restrict an 
entity's rendering capacity such that it can only affect the component of the render tree that it represents?
--}

type Spec :: Row SlotData -> Type -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type 
data Spec slots rendered context state query m where 
  MkSpec :: Forall slots SlotOrdC => 
    { initialState   :: state -- For existential-ey reasons this has to be a function
    , handleQuery    :: AlgebraQ query :~> EntityM slots context state query m
    , render         :: state -> Maybe rendered -- I don't like this being IO () but i can't see a way around it -_-
    , slots          :: Proxy slots 
    } -> Spec slots rendered context state query m 

defaultRender :: forall slots state  context query m 
               . state -> EntityM slots  context state query m ()
defaultRender = const . pure $ ()

queryAlgebra :: forall slots r s q m 
        . Functor m
       => ( q ~> EntityM slots r s q m)
       -> (AlgebraQ q :~> EntityM slots r s q m)
queryAlgebra eval = NT go 
  where 
    go :: forall x. AlgebraQ q x -> EntityM slots r s q m x
    go (Q q) = unCoyoneda (\g -> fmap  g . eval) q

    unCoyoneda :: forall (q :: Type -> Type) (a :: Type) (r :: Type)
                . (forall (b :: Type). (b -> a) -> q b -> r)
               -> Coyoneda q a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

prototype :: Forall slots SlotOrdC 
          => Spec slots rendered context state query m 
          -> Prototype slots rendered context query m 
prototype e = Prototype e 




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
                             ,KnownSymbol lbl
                             ,Ord i)

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
           . MonadIO m =>  EvalState slots r cxt st q  m -> EntityStore r q m 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState r q m -> Transformer r q m
    go ex@(ExEvalState es@EvalState {..}) = Transformer $ \qx -> do  
      let (EntityM ai) = apNT (handleQuery _entity) (Q . liftCoyoneda $ qx)
      let  st          = foldF (evalF es) ai
      ST.runStateT st ex

-- don't export this
run :: forall x m q r. MonadIO m => q x -> Entity r m q -> m x
run i (Entity tv) = do
  e <- liftIO $ readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  liftIO . atomically . writeTVar tv $ newObj -- write new store thingy to tvar 
  pure x 

-- internal, don't export
getSlot :: forall l i cxt r q q' m' slots st
         . (Functor m'
         ,  MonadIO m' 
         ,  ChildC l i r q' m' slots) 
        => EntityM slots cxt st q m' (M.Map i (Entity r m' q'))
getSlot = EntityM . liftF $ Child (Slot :: Slot l slots q' m' i r) id 

getSurface :: forall l i cxt r q q' m' slots st 
            . (ChildC l i r q' m' slots, Functor m', MonadIO m')
           => EntityM slots cxt st q m' (M.Map i r)
getSurface = EntityM . liftF $ Surface (Slot :: Slot l slots q' m' i r) id 

type Tell q = () -> q ()

mkTell :: Tell q -> q ()
mkTell q  = q ()

-- deleteChildEntity :: (ChildC lbl i r q' m' slots, Ord i, MonadIO m')
-- deleteChildEntity = undefined 

tell :: forall lbl i r q' m' q slots state context
      . (ChildC lbl i r q' m' slots, Ord i, MonadIO m')
     => i 
     -> Tell q' 
     -> EntityM slots context state q m' ()
tell i q = do 
  mySlot <- getSlot @lbl @i @context @r @q  @q' @m' 
  case M.lookup i mySlot of  
    Nothing -> pure () 
    Just e  -> do 
      lift (run (mkTell q) e)
      liftIO (renderE e) >>= \case 
        Nothing -> do 
          mySurface <- getSurface @lbl @i @context @r @q @q' @m' 
          undefined
        Just _ -> undefined 

--tellAll :: forall m q t r. (Traversable t, MonadIO m) => Tell q -> t (Entity r m q) -> m ()
--tellAll q es = mapM_ (mkTell q) es  

type Request q a = (a -> a) -> q a 

mkRequest :: Request q x -> q x
mkRequest q = q id 

renderE :: Entity r m q -> IO (Maybe r) 
renderE (Entity tv) = do 
  e <- liftIO $ readTVarIO tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> pure $ render _entity _state 

evalF :: forall slots' r' cxt' st' q'  m' a' 
    .  MonadIO m' 
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

  Child slot f -> case slot of -- need this for type inference, it's not superfluous here 
    Slot -> pure . f $ _storage .! slotLabel slot

  Surface slot f -> case slot of 
    Slot -> pure . f $ _renderTree .! slotLabel slot 

  Create slot i e a -> case slot of 
    Slot -> do 
      liftIO (renderE e) >>= \case 
        Nothing -> pure a 
        Just x  -> do
          let l = slotLabel slot 
          let oldSurface = _renderTree .! l
          let oldSlot    = _storage    .! l
          let newSlot    = M.insert i e oldSlot
          let newSurface = M.insert i x oldSurface 
          ST.modify' $ \_ -> 
            ExEvalState $ EvalState {_storage = R.update l newSlot _storage
                                    ,_renderTree = R.update l newSurface _renderTree
                                    ,..} 
          pure a 
  
  Delete slot i a -> case slot of 
    Slot -> do 
      let l = slotLabel slot 
      let oldSurface = _renderTree .! l
      let oldSlot    = _storage    .! l
      let newSlot    = M.delete i oldSlot
      let newSurface = M.delete i oldSurface 
      ST.modify' $ \_ -> 
        ExEvalState $ EvalState {_storage = R.update l newSlot _storage
                                ,_renderTree = R.update l newSurface _renderTree 
                                ,..}
      pure a 
