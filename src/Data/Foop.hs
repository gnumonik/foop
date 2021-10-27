{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

{--

It really sucks that this all has to be in one module, but it does. 

EntityF depends on Slot which depends on Entity which depends on EntityF -_-

If we get a typechecker loop, need to paramaterize Slot over a generic kind w/ the same 
type args as Entity. This will be really ugly. I hope it doesn't happen. 
--}

module Data.Foop  ( EntityM(..)
                  , MonadLook(..)
                  , type SlotData
                  , Slot(..)
                  , type MkSlot 
                  , type SlotOrdC 
                  , Prototype(..)
                  , type (~>)
                  , AlgebraQ(..)
                  , Spec(..)
                  , queryHandler
                  , type ChildStorage 
                  , type MkStorage 
                  , type ChildC 
                  , type StorageConstraint 
                  , type RenderConstraint 
                  , type MkRenderTree 
                  , new_
                  , type Tell 
                  , type Request  
                  , mkTell 
                  , mkRequest
                  , tell 
                  , tellAll 
                  , request 
                  , requestAll 
                  , delete 
                  , create
                  , emptySlots
                  , prototype
                  , activate
                  , query
                  , type Object) where

import Control.Monad.Free.Church ( liftF, F(..), foldF ) 
import Control.Monad.State.Class ( MonadState(state) ) 
import Control.Monad.Trans.Class ( MonadTrans(..) ) 
import Control.Monad.Reader ( MonadIO(..), MonadTrans(..) ) 
import Control.Monad.IO.Class ( MonadIO(..) ) 
import Data.Kind ( Type, Constraint ) 
import Data.Bifunctor ( Bifunctor(first) ) 
import Data.Functor.Coyoneda ( Coyoneda(..), liftCoyoneda )
import Data.Constraint ( Constraint ) 
import Data.Functor (($>))
import Data.Row.Records
    ( KnownSymbol,
      Extend,
      Empty,
      Row,
      Rec,
      Label(..),
      (.!),
      Forall,
      HasType,
      WellBehaved )
import GHC.TypeLits (Symbol)
import Data.Row
    ( KnownSymbol,
      Empty,
      Row,
      Rec,
      Label(..),
      (.!),
      Forall,
      HasType,
      WellBehaved ) 
import Data.Row.Internal
    ( KnownSymbol,
      Extend,
      Empty,
      Row(..),
      Label(..),
      Forall,
      HasType,
      WellBehaved,
      LT(..) )
import qualified Data.Map.Strict as M
import qualified Data.Row.Records as R 
import Data.Default ( Default(..) ) 
import Data.Proxy (Proxy(..))
import Data.Singletons.TypeLits (Symbol)
import qualified Control.Monad.State.Class as S 
import Control.Comonad.Store
    ( Comonad(extract), store, ComonadStore(pos), Store )
import Control.Concurrent.STM
    ( atomically, newTVarIO, readTVarIO, writeTVar, TVar, STM, readTVar, newTVar, TMVar, putTMVar, TBQueue, readTBQueue, newTBQueueIO, mkWeakTVar, newEmptyTMVar, writeTBQueue, takeTMVar )
import qualified Control.Monad.State.Strict as ST
import Data.Maybe (catMaybes)
import Control.Monad (forever)
import System.Mem.Weak 
import Control.Concurrent.Async 
import Control.Applicative ( Applicative(liftA2) ) 

----------------------------------------------------
----------------------------------------------------
---- Fundamental types (Slot, EntityF) + instances 
----------------------------------------------------
----------------------------------------------------

-- can't add a SlotData argument to this (type cycle) so i need to find a way to do this w/ 
-- data or figure something else out. bleh. 
type SlotData = (Type,Type, Type -> Type)

type Slots = Row SlotData 

type MkSlot :: Type -> Type -> (Type -> Type) -> SlotData 
type MkSlot surface index query = '(surface,index,query) 

class Monad m => MonadLook l m where 
  look :: m l 

data Slot :: Symbol -> Row SlotData -> (Type -> Type) -> Type -> Type -> Type where 
  Slot :: ( HasType l (M.Map i (Entity r q)) (MkStorage slots)
          , HasType l (M.Map i r) (MkRenderTree slots)
          , KnownSymbol l 
          , Ord i) => Slot l slots q i r

slotLabel :: forall slots q i r l. Slot l slots q i r -> Label l 
slotLabel Slot = Label @l

type EntityF :: Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
data EntityF slots  state query m a where 
  State  :: (state -> (a,state)) -> EntityF slots  state query m a
 
  Lift   :: m a -> EntityF slots state query m a

  Query  :: Coyoneda query a -> EntityF slots state query m a

  Child  :: Slot l slots q i r -> (M.Map i (Entity r q) -> a) -> EntityF slots state query m a 

  Surface:: Slot l slots q i r -> (M.Map i r -> a) -> EntityF slots state query m a 

  Create :: Slot l slots q i r -> i -> (TBQueue BoxedIO -> STM (Entity r q)) -> a -> EntityF slots state query m a 

  Delete :: Slot l slots q i r -> i -> a -> EntityF slots state query m a 

  -- 3rd arg needs to be (RenderView r slots -> a)
  Render :: Slot l slots q i r -> i -> a -> EntityF slots state query m a

instance Functor m => Functor (EntityF slots state query m) where
  fmap f = \case 
    State k          -> State (first f . k)
    Lift ma          -> Lift (f <$> ma)
    Query qb         -> Query $ fmap f qb 
    Child key g      -> Child key $ fmap f g 
    Surface key g    -> Surface key $ fmap f g  
    Create key i e a -> Create key i e (f a)
    Delete key i a   -> Delete key i (f a) 
    Render key i a   -> Render key i (f a)

newtype EntityM slots state query m a = EntityM (F (EntityF slots state query m) a) deriving (Functor, Applicative, Monad)  

instance Functor m => MonadState s (EntityM slots s q m) where 
  state f = EntityM . liftF . State $ f 

instance  MonadIO m => MonadIO (EntityM slots s q m) where 
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM slots s q ) where 
  lift = EntityM . liftF . Lift 

----------------------------------------------------
----------------------------------------------------
---- Prototype + Spec, related constraints 
----------------------------------------------------
----------------------------------------------------

type SlotOrdC :: (Type, Type, Type -> Type) -> Constraint 
class SlotOrdC slot where 
instance Ord i => SlotOrdC '(r,i,q) 

data Prototype :: Row SlotData -> Type ->  (Type -> Type) -> Type where 
  Prototype :: Forall slots SlotOrdC 
            => Spec slots surface  state query 
            -> Prototype slots surface query 

type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

newtype AlgebraQ query a =  Q (Coyoneda query a) 

type Spec :: Row SlotData -> Type -> Type -> (Type -> Type) ->  Type 
data Spec slots surface state query where 
  MkSpec :: Forall slots SlotOrdC => 
    { initialState   :: state -- For existential-ey reasons this has to be a function
    , handleQuery    :: AlgebraQ query :~> EntityM slots state query STM
    , render         :: state -> Maybe surface -- I don't like this being IO () but i can't see a way around it -_-
    , slots          :: Proxy slots 
    } -> Spec slots surface state query 

emptySlots :: Proxy Empty 
emptySlots = Proxy 

defaultRender :: forall slots state query m 
               . state -> EntityM slots state query m ()
defaultRender = const . pure $ ()

queryHandler :: forall slots s q m 
        . Functor m
       => ( q ~> EntityM slots s q m)
       -> (AlgebraQ q :~> EntityM slots s q m)
queryHandler eval = NT go 
  where 
    go :: forall x. AlgebraQ q x -> EntityM slots s q m x
    go (Q q) = unCoyoneda (\g -> fmap  g . eval) q

    unCoyoneda :: forall (q :: Type -> Type) (a :: Type) (r :: Type)
                . (forall (b :: Type). (b -> a) -> q b -> r)
               -> Coyoneda q a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

prototype :: Forall slots SlotOrdC 
          => Spec slots surface state query 
          -> Prototype slots surface query 
prototype = Prototype 

type ChildStorage :: Row SlotData -> Type 
type ChildStorage slots = Rec (MkStorage slots)

type MkStorage ::  Row SlotData -> Row Type 
type family MkStorage rt where 
  MkStorage (R lts) = MkStorage_ lts 

type MkStorage_ :: [LT (Type,Type,Type -> Type)] -> Row Type  
type family MkStorage_ lts where 
  MkStorage_ '[] = Empty 
  MkStorage_ (l :-> '(r,i,q) ': lts) = Extend l (M.Map i (Entity r q)) (MkStorage_ lts)

type ChildC :: Symbol -> Type -> Type -> (Type -> Type) ->  Row SlotData -> Constraint 
type family ChildC childLabel index surface q slots where 
  ChildC lbl i r q slots = (HasType lbl (M.Map i (Entity r q)) (MkStorage slots)
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

type MkRenderTree_ :: [LT (Type,Type,Type -> Type)] -> Row Type 
type family MkRenderTree_ slots where
  MkRenderTree_ '[] = Empty 
  MkRenderTree_ (l :-> '(r,i,q) ': lts) = Extend l (M.Map i r) (MkRenderTree_ lts)

type RenderView :: Type -> Row SlotData -> Type 
data RenderView r slots = RenderView r (Rec (MkRenderTree slots))

instance (Forall (MkRenderTree slots) Show, Show r) => Show (RenderView r slots) where 
  show (RenderView r tree) = "RenderView " <> show r <> " " <> show tree 

type SlotConstraint slots = (StorageConstraint slots, RenderConstraint slots)

mkStorage :: forall slots
           . StorageConstraint slots 
          => Proxy slots  -> Rec (MkStorage slots)
mkStorage proxy = R.default' @Default def

mkRenderTree :: forall slots 
              . SlotConstraint slots 
            => Proxy slots -> Rec (MkRenderTree slots)
mkRenderTree proxy = R.default' @Default def 

----------------------------------------------------
----------------------------------------------------
---- Evaluation + User-facing functions 
----------------------------------------------------
----------------------------------------------------

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState slots surface st q 
  = EvalState {
      _entity     :: Spec slots surface st q 
    , _state      :: st 
    , _storage    :: Rec (MkStorage slots)
    , _renderTree :: Rec (MkRenderTree slots)
    , _ioQ        :: TBQueue BoxedIO
  }

data ExEvalState :: Type -> (Type -> Type) ->  Type where 
  ExEvalState :: EvalState slots surface st q  
              -> ExEvalState surface q 

withExEval :: forall q surface  r
            . ExEvalState surface q 
            -> (forall slots cxt st. EvalState slots surface st q -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

new_ :: forall slots query surface 
        . (SlotConstraint slots)
       => Prototype slots surface query 
       -> TBQueue BoxedIO
       -> STM (Entity surface query)  
new_ (Prototype espec@MkSpec{..}) q = newTVar e' >>= \eStore -> pure $  Entity eStore 
  where 
    !evalSt = initE espec q

    !e' = mkEntity_ evalSt 

initE :: SlotConstraint slots 
      => Spec slots r  st q 
      -> TBQueue BoxedIO
      -> EvalState slots r st q 
initE espec@MkSpec{..} ioQ  
  = EvalState {_entity     = espec 
              ,_state      = initialState 
              ,_storage    = mkStorage slots
              ,_renderTree = mkRenderTree slots
              ,_ioQ        = ioQ}  

newtype Transformer r q = Transformer {transform :: forall x. q x -> STM (x,ExEvalState r q)}

type EntityStore r q = Store (ExEvalState r q ) (Transformer r q)

-- This is quite different from Halogen (which is the basis for all the Prototype stuff) so, quick explanation: 
-- EntityS is a TVar that holds a store comonad which spits out a *function* from the input to m newEvalState
-- This is kind of a weird construction but because StateT isn't a comonad and we need a StateT from which we can *extract* the state at any time
-- (for queries)

newtype Entity r q = Entity {entity :: TVar (EntityStore r q)}

mkEntity_ :: forall slots surface  st query
           . EvalState slots surface st query -> EntityStore surface query 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState r q -> Transformer r q 
    go ex@(ExEvalState es@EvalState {..}) = Transformer $ \qx -> do  
      let (EntityM ai) = apNT (handleQuery _entity) (Q . liftCoyoneda $ qx)
      let  st          = foldF (evalF es) ai
      ST.runStateT st ex

-- don't export this
run :: forall x q r. q x -> Entity r q -> STM x
run i (Entity tv) = do
  e <- readTVar tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  writeTVar tv newObj -- write new store thingy to tvar 
  pure x 

-- internal, don't export
getSlot :: forall l i  r q q' slots st
         . (ChildC l i r q' slots) 
        => EntityM slots st q STM (M.Map i (Entity r q'))
getSlot = EntityM . liftF $ Child (Slot :: Slot l slots q' i r) id 

-- don't export 
getSlot' ::  Slot l slots q i r
         -> EntityM slots  state query STM (M.Map i (Entity r q))
getSlot' slot = EntityM . liftF $ Child slot id 

-- don't export 
getSurface :: forall l i r q q' m' slots st 
            . (ChildC l i r q' slots, Functor m', MonadIO m')
           => EntityM slots st q m' (M.Map i r)
getSurface = EntityM . liftF $ Surface (Slot :: Slot l slots q' i r) id 

type Tell q = () -> q ()

mkTell :: Tell q -> q ()
mkTell q  = q ()

tell :: forall lbl i r q' q slots state
      . (ChildC lbl i r q' slots, Ord i)
     => i 
     -> Tell q' 
     -> EntityM slots state q STM ()
tell i q = do 
  mySlot <- getSlot @lbl
  case M.lookup i mySlot of  
    Nothing -> pure () 
    Just e  -> do 
      lift (run (mkTell q) e)
      renderChild @lbl i

tellAll :: forall lbl i r q' q slots state context
      . (ChildC lbl i r q' slots, Ord i)
     => Tell q' 
     -> EntityM slots state q STM () 
tellAll q = do 
  mySlot <- M.keys <$> getSlot @lbl 
  mapM_ (\i -> tell @lbl i q) mySlot
 
type Request q a = (a -> a) -> q a 

request :: forall lbl i r q' q slots state context x
      . (ChildC lbl i r q' slots, Ord i)
     => i 
     -> Request q' x  
     -> EntityM slots state q STM (Maybe x)
request i q = do 
  mySlot <- getSlot @lbl  
  case M.lookup i mySlot of 
    Nothing -> pure Nothing 
    Just e  -> do 
      o <- lift (run (mkRequest q) e)
      renderChild @lbl i 
      pure (Just o)

requestAll :: forall lbl i r q' q slots state context x
      . (ChildC lbl i r q' slots, Ord i)
     => Request q' x  
     -> EntityM slots state q STM [x]
requestAll q = do 
  mySlot <- M.keys <$> getSlot @lbl 
  catMaybes <$> mapM (\i -> request @lbl i q) mySlot 

mkRequest :: Request q x -> q x
mkRequest q = q id 

renderE :: Entity r q -> STM (Maybe r) 
renderE (Entity tv) = do 
  e <- readTVar tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> pure $ render _entity _state 

evalF :: forall slots' r' st' q'  m' a' 
    .  EvalState slots' r' st' q'  
    -> EntityF slots' st' q' STM a'
    -> ST.StateT (ExEvalState r' q') STM a' 
evalF EvalState{..} = \case 

  State f -> case f _state of 
    (a,newState) -> do 
        let newSurface = render _entity newState 
        ST.modify' $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Query q -> case apNT (handleQuery _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  

  Child slot f -> case slot of -- need this for type inference, it's not superfluous here 
    Slot -> pure . f $ _storage .! slotLabel slot

  Surface slot f -> case slot of 
    Slot -> pure . f $ _renderTree .! slotLabel slot 

  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot i e' a -> case slot of 
    Slot -> do 
      e <- lift $ e' _ioQ
      lift (renderE e) >>= \case 
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

  Render slot i a -> case slot of 
    Slot -> do
      let l = slotLabel slot 
      let oldSurface = _renderTree .! l
      let oldSlot    = _storage    .! l
      let newSurface = M.insert i oldSurface 
      case M.lookup i oldSlot of 
        Nothing -> pure a 
        Just e  -> do 
          lift (renderE e) >>= \case 
            Nothing -> evalF EvalState{..} (Delete slot i a)
            Just r -> do 
              let newSurface = M.insert i r oldSurface 
              ST.modify' $ \_ -> 
                ExEvalState $ EvalState {_renderTree = R.update l newSurface _renderTree
                                        ,..}
              pure a  

delete :: forall lbl i r q'  q slots state 
      . (ChildC lbl i r q' slots, Ord i)
     => i 
     -> EntityM slots state q STM ()
delete i = EntityM . liftF $ Delete (Slot :: Slot lbl slots q' i r) i () 

create :: forall lbl i r q' q slots slots' state
      . (ChildC lbl i r q' slots, Ord i, SlotConstraint slots')
     => i
     -> Prototype slots' r q' 
     -> EntityM slots state q STM ()
create i p = EntityM . liftF $ Create (Slot :: Slot lbl slots q' i r) i (new_ p) ()

-- internal, don't export
renderChild :: forall lbl i r q' q slots state 
      . (ChildC lbl i r q' slots, Ord i)
     => i
     -> EntityM slots state q STM ()
renderChild i = EntityM . liftF $ Render (Slot :: Slot lbl slots q' i r) i ()

-- don't export 
type Object :: Type -> (Type -> Type) -> Type 
newtype Object r q = Object (Entity r q)

----------------------------------------------------
----------------------------------------------------
---- Top-Level Object Stuff
----------------------------------------------------
----------------------------------------------------

activate :: (SlotConstraint slots)
            => Prototype slots surface query 
            -> IO (Object surface query)
activate p = do 
  ioQ     <- newTBQueueIO 10000
  e@(Entity tv) <- atomically $ new_ p ioQ
  agent   <- async (ioAgent ioQ)
  _       <- mkWeakTVar tv (uninterruptibleCancel agent)
  pure (Object e)

query :: Object surface query 
      -> query x 
      -> STM x 
query (Object e) q = run q e

viewSurface :: MonadIO m => Object surface query -> m surface 
viewSurface (Object (Entity e)) 
  = liftIO (readTVarIO e) >>= \eStore ->
    case pos eStore of 
      ExEvalState EvalState{..} -> undefined

-- don't export 
data BoxedIO :: Type where 
  BoxedIO :: IO a -> TMVar a -> BoxedIO 

ioAgent :: TBQueue BoxedIO -> IO ()
ioAgent ioQ = forever $ do 
  atomically (readTBQueue ioQ) >>= \case --better type inference 
    BoxedIO io tmv -> performIO io tmv 

performIO :: IO x -> TMVar x -> IO ()
performIO io tmv = do 
  a <- io 
  atomically $ putTMVar tmv a