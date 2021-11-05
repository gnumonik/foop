{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Data.Foop.Eval where

import Data.Foop.Types
import qualified Control.Monad.State as ST
import qualified Data.Map as M
import Control.Monad.IO.Class
import qualified Data.Row.Records as R
import Control.Monad.Trans.Class
import Data.Row
import Data.Foop.Prototype
import Data.Functor.Coyoneda ( Coyoneda(..), liftCoyoneda )
import Control.Monad.Free.Church
import Control.Comonad.Store
import Control.Concurrent.STM
import Data.Maybe
import Data.Kind (Type)
import Data.Functor.Constant
import Data.Row.Internal
import Data.Data
import Control.Monad.Identity
import Data.Constraint
import GHC.TypeLits (Symbol)
import qualified Data.Constraint.Forall as DC
import Data.Constraint.Unsafe
import Data.Bifunctor
import Data.Row.Dictionaries
import Data.Functor.Yoneda
import Data.Functor.Compose
import Data.Default
import Control.Lens (over, set, view)
import GHC.IO (unsafePerformIO)
import Control.Lens.Getter
import Control.Lens.Fold
import Data.Foop.Dictionary
import Data.Foop.Slot

-- | Extracts a label `l` from a `SlotKey l slots q i r`
slotLabel :: forall l slots slot . SlotKey l slots slot -> Label l
slotLabel SlotKey = Label @l

-- | Existenial eliminator for an ExEvalState 
withExEval :: forall query surface slots context r
            . ExEvalState context surface slots query
            -> (forall state. EvalState context slots surface state query -> r)
            -> r
withExEval (ExEvalState e) f = f e

-- | Constructs an entity from a model
new_ :: forall index surface slots query context c
        . (Ord index, SlotOrdC context,Forall slots SlotOrdC, c context)
       => TVar (RenderLeaf context) 
       -> Model surface slots query c
       -> IO (Entity '(index,surface,RenderTree slots,query))
new_ cxt (Model p) = case p   of 
  espec@MkSpec{..} -> do
    let evalSt = initE cxt espec
    eStore <- newTVarIO $  mkEntity_ evalSt
    pure $  Entity eStore

-- | Constructs an entity from a model
new_' :: forall index surface slots query context state 
        . (Ord index, SlotOrdC context, Forall slots SlotOrdC)
       => Spec slots surface state query context 
       -> Rec (MkStorage slots) 
       -> surface 
       -> RenderTree slots 
       -> TVar (RenderLeaf context) 
       -> IO (Entity '(index,surface,RenderTree slots,query))
new_' spec@MkSpec{..} storage surface tree cxt  =  do
    let evalSt = EvalState {_entity  = spec 
                           ,_state   = initialState 
                           ,_storage = storage 
                           ,_surface = surface 
                           ,_context = cxt }
    eStore <- newTVarIO $  mkEntity_ evalSt
    pure $  Entity eStore

-- | Initializes an EvalState given a Spec 
initE :: forall slots r st q cxt
       . (SlotConstraint slots,SlotOrdC cxt)
      => TVar (RenderLeaf cxt) 
      -> Spec slots r st q cxt
      -> EvalState cxt slots r st q 
initE cxt espec@MkSpec{..}
  =
    EvalState {_entity     = espec
              ,_state      = initialState
              ,_storage    = mkStorage slots
              ,_surface    = render renderer initialState
              ,_context    = cxt}

-- | Constructs and EntityStore from an EvalState 
mkEntity_ :: forall slots surface  st query context 
           . EvalState context slots surface st query -> EntityStore context surface slots query
mkEntity_ e = store go (ExEvalState e)
  where
    go :: ExEvalState cxt r s q -> Transformer cxt r s q
    go ex@(ExEvalState es@EvalState {..}) = Transformer $ \qx -> do
      let (EntityM ai) = apNT (handleQuery _entity) (Q . liftCoyoneda $ qx)
      let  st          = foldF (evalF es) ai
      ST.runStateT st ex

-- don't export this
-- | Runs an entity. For internal use only; you should use `tell` and `request` instead of this. 
run :: forall slot q x. QueryOf slot q => q x -> Entity slot -> IO x
run i (Entity tv) = do
  e <- readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  atomically $ writeTVar tv newObj -- write new store thingy to tvar 
  pure x

-- internal, don't export
-- | Retrieves the map of the entity's children. For internal use.
getSlot :: forall  label slots slot st q context
         . (ChildC label slots slot, SlotConstraint slots)
        => EntityM context slots st q IO (StorageBox slot)
getSlot = EntityM . liftF $ Child (SlotKey :: SlotKey label slots slot) id

-- don't export 
-- | `getSlot` but with a SlotKey (which serves as a dictionary for ChildC) instead of the ChildC constraint 
getSlot' ::  SlotKey label slots slot
         -> EntityM context slots state query IO (StorageBox slot)
getSlot' slot = EntityM . liftF $ Child slot id



-- | Construct a `Tell` query from a data constructor of a query algebra
mkTell :: Tell q -> q ()
mkTell q  = q ()

-- | `tell i q` takes an index/key for a child entity and a data constructor of that 
--   entity's algebra, and returns a monadic action in the parent entity which 
--   executes the query. 
--
--   Note: The slot label for the child entity is implicit; this requires a type application 
--   for the label (it should *only* require one for the label). 
-- 
--   E.g. `tell @"childLabel" 123 MyQuery`
tell :: forall label slots i su cs q state query cxt 
      . (ChildC label slots '(i,su,RenderTree cs,q), SlotConstraint slots)
     => i
     -> Tell q
     -> EntityM cxt slots state query IO ()
tell i = tell_ @label (Indexed Index i)

tell_ :: forall label slots i su cs q state query cxt 
      . (ChildC label slots '(i,su,RenderTree cs,q), SlotConstraint slots)
     => Indexed '(i,su,RenderTree cs,q)
     -> Tell q
     -> EntityM cxt slots state query IO ()
tell_ i q = do
  MkStorageBox mySlot <- getSlot @label
  case M.lookup  i mySlot of
    Nothing -> pure ()
    Just e  -> do
      lift (run (mkTell q) e)
      pure ()

-- | `tellAll q` executes a tell query for every child entity at a given slot. 
--   
--    Like `tell`, this requires a type application for the child label. 
-- 
--    E.g. `tell @"childLabel" MyQuery` 
tellAll :: forall label i su cs q slots state query cxt
      . (ChildC label slots '(i,su,RenderTree cs,q), SlotConstraint slots)
     => Tell q
     -> EntityM cxt slots state query IO ()
tellAll q = do
  MkStorageBox mySlot <- getSlot @label @slots @'(i,su,RenderTree cs,q)
  let slotKeys = M.keys mySlot
  mapM_ (\i -> pure (M.lookup i mySlot) >>= \case
                Nothing -> pure ()
                Just x  -> lift . run (mkTell q) $ x) slotKeys

-- | `request i q` takes an index/key for a child entity and a data constructor of 
--   that entity's algebra, and returns a monadic action in the parent entity which executes the 
--   query and returns (Maybe) the result of the query. 
--
--   Like `tell`, this requires a type application for the child label. 
--   
--   e.g. `request @"childLabel" 123 MyQuery`   
request :: forall label i su cs q slots state query x cxt 
      . (ChildC label slots '(i,su,RenderTree cs,q), SlotConstraint slots)
     => i
     -> Request q x
     -> EntityM cxt slots state query IO (Maybe x)
request i = request_ @label (Indexed Index i)

request_ :: forall label i su cs q slots state query x cxt
      . (ChildC label slots '(i,su,RenderTree cs,q), SlotConstraint slots)
     => Indexed '(i,su,RenderTree cs,q)
     -> Request q x
     -> EntityM cxt slots state query IO (Maybe x)
request_ i q = do
  MkStorageBox mySlot <- getSlot @label
  case M.lookup i mySlot of
    Nothing -> pure Nothing
    Just e  -> do
      o <- lift (run (mkRequest q) e)
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall label i su cs q slots state query cxt x 
      . (ChildC label slots '(i,su,RenderTree cs,q), SlotConstraint slots)
     => Request q x
     -> EntityM cxt slots state query IO [x]
requestAll q = do
  MkStorageBox mySlot <- getSlot @label
  let slotKeys = M.keys mySlot
  catMaybes <$> mapM (\i -> request_ @label i q) slotKeys

mkRequest :: Request q x -> q x
mkRequest q = q id

evalF :: forall slots' r' st' q' a' cxt'
    .  EvalState cxt' slots' r' st' q'
    -> EntityF cxt' slots' st' q' IO a'
    -> ST.StateT (ExEvalState cxt' r' slots' q') IO a'
evalF EvalState{..} = \case

  State f -> case f _state of
    (a,newState) -> do
        newSurface <- renderS newState
        ST.modify' $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a

  Lift ma -> lift ma

  Context g -> do 
    cxt <- liftIO $ readTVarIO _context 
    pure $ g cxt

  Query q -> case apNT (handleQuery _entity) (Q q ) of
    EntityM ef -> foldF (evalF (EvalState {..})) ef

  Child slot f ->  pure . f $ lookupStorage slot _storage

  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot i e' a -> case slot of
    SlotKey -> do
      e <- liftIO $ new_ _context e'
      lift (atomically $ observeE e) >>= \x@(MkRenderLeaf su cs) -> do
          ST.modify' $ \_ -> withDict (deriveStoreHas slot)
            ExEvalState $ EvalState {_storage =  modifyStorage slot (\(MkStorageBox m) ->
                                                      MkStorageBox  $ M.insert (Indexed Index i) e m) _storage
                                    ,..}
          pure a

  Delete slot i a -> case slot of
    SlotKey -> do
      ST.modify' $ \_ ->
        ExEvalState $ EvalState {_storage = modifyStorage slot (\(MkStorageBox  m) -> MkStorageBox $ M.delete (Indexed Index i) m) _storage
                                ,..}
      pure a
 where
   renderS :: MonadIO n => st' -> n r'
   renderS st = do
     let newSurface = render (renderer _entity)  st
     liftIO $ onRender (renderer _entity) newSurface
     pure newSurface

-- | Deletes a child entity (and its rendered output in the renderTree).
--   
--   Requires a type application for the label 
delete :: forall label slots state i su cs q query cxt
      . (ChildC label slots '(i,su,RenderTree cs,q), Forall slots SlotOrdC)
     => i
     -> EntityM cxt slots state query IO ()
delete i = EntityM . liftF $ Delete (SlotKey :: SlotKey label slots '(i,su,RenderTree cs,q)) i ()

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.
create :: forall label slots i su cs q state query cxt c
      . (ChildC label slots '(i,su,RenderTree cs,q), c cxt)
     => i
     -> Model su cs q c
     -> EntityM cxt slots state query IO ()
create i p = EntityM . liftF $ Create (SlotKey :: SlotKey label slots '(i,su,RenderTree cs,q))  i p ()

