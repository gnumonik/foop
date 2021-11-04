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
import Unsafe.Coerce
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

-- | Extracts a label `l` from a `SlotBox l slots q i r`
slotLabel :: forall l slots slot . SlotBox l slots slot-> Label l 
slotLabel SlotBox = Label @l

-- | Existenial eliminator for an ExEvalState 
withExEval :: forall query surface slots r
            . ExEvalState surface slots query 
            -> (forall state. EvalState slots surface state query -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

-- | Constructs an entity from a prototype
new_ :: forall index surface slots query 
        . Ord index 
       => Prototype surface slots query 
       -> IO (Entity '(index,surface,RenderTree slots,query))  
new_ (Prototype espec@MkSpec{..}) = do 
    evalSt <- initE espec  
    eStore <- newTVarIO $  mkEntity_ evalSt 
    pure $  Entity eStore 

-- | Initializes an EvalState given a Spec 
initE :: forall slots r st q 
       . SlotConstraint slots 
      => Spec slots r st q 
      -> IO (EvalState slots r st q) 
initE espec@MkSpec{..} 
  = pure (mkStorage slots) >>= \storage ->
    toSurface slots storage >>= \surface -> pure $ 
    EvalState {_entity     = espec 
              ,_state      = initialState 
              ,_storage    = storage
              ,_renderTree = MkRenderTree surface}  

-- | Constructs and EntityStore from an EvalState 
mkEntity_ :: forall slots surface  st query 
           . EvalState slots surface st query -> EntityStore surface slots query 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState r s q -> Transformer r s q 
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
getSlot :: forall label slots slot st q 
         . (ChildC label slots slot) 
        => EntityM slots st q IO (StorageBox slot)
getSlot = EntityM . liftF $ Child (SlotBox :: SlotBox label slots slot) id 

-- don't export 
-- | `getSlot` but with a SlotBox (which serves as a dictionary for ChildC) instead of the ChildC constraint 
getSlot' ::  SlotBox label slots slot 
         -> EntityM slots state query IO (StorageBox slot)
getSlot' slot = EntityM . liftF $ Child slot id 

-- don't export 
-- | Like `getSlot` but for the rendered surface 
getSurface :: forall label slots slot st q 
            . ChildC label slots slot
           => EntityM slots st q IO (RenderNode slot)
getSurface = EntityM . liftF $ Surface (SlotBox :: SlotBox label slots slot) id 

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
tell :: forall label slots i su cs q state query 
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => i
     -> Tell q
     -> EntityM slots state query IO ()
tell i = tell_ @label (Indexed Index i) 

tell_ :: forall label slots i su cs q state query 
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Indexed '(i,su,RenderTree cs,q)
     -> Tell q
     -> EntityM slots state query IO ()
tell_ i q = do 
  MkStorageBox mySlot <- getSlot @label
  case M.lookup  i mySlot of  
    Nothing -> pure () 
    Just e  -> do 
      lift (run (mkTell q) e)
      _ <- renderChild @label (unIndexed i)
      pure ()

-- | `tellAll q` executes a tell query for every child entity at a given slot. 
--   
--    Like `tell`, this requires a type application for the child label. 
-- 
--    E.g. `tell @"childLabel" MyQuery` 
tellAll :: forall label i su cs q slots state query
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Tell q
     -> EntityM slots state query IO () 
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
request :: forall label i su cs q slots state query x
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => i
     -> Request q x  
     -> EntityM slots state query IO (Maybe x)
request i = request_ @label (Indexed Index i)

request_ :: forall label i su cs q slots state query x
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Indexed '(i,su,RenderTree cs,q)
     -> Request q x  
     -> EntityM slots state query IO (Maybe x)
request_ i q = do 
  MkStorageBox mySlot <- getSlot @label 
  case M.lookup i mySlot of 
    Nothing -> pure Nothing 
    Just e  -> do 
      o <- lift (run (mkRequest q) e)
      _ <- renderChild @label (unIndexed i) 
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall label i su cs q slots state query x
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Request q x  
     -> EntityM slots state query IO [x]
requestAll q = do 
  MkStorageBox mySlot <- getSlot @label
  let slotKeys = M.keys mySlot 
  catMaybes <$> mapM (\i -> request_ @label i q) slotKeys 

mkRequest :: Request q x -> q x
mkRequest q = q id 

-- | Given an Entity, renders its surface. Doesn't update anything, but does run the IO action.
renderE :: forall i su cs q 
         .  Entity '(i,su,RenderTree cs,q)
         -> IO (RenderLeaf '(i,su,RenderTree cs,q))
renderE (Entity tv) = do 
  e <- readTVarIO tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> do 
      let surface = render (renderer  _entity)  _state 
      onRender (renderer _entity) surface 
      pure $ MkRenderLeaf surface _renderTree

evalF :: forall slots' r' st' q' a' 
    .  EvalState slots' r' st' q'
    -> EntityF slots' st' q' IO a'
    -> ST.StateT (ExEvalState r' slots' q') IO a' 
evalF EvalState{..} = \case 

  State f -> case f _state of 
    (a,newState) -> do 
        let newSurface = render (renderer _entity)  newState 
        liftIO $ onRender (renderer _entity) newSurface 
        ST.modify' $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Query q -> case apNT (handleQuery _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  

  Child slot f ->  pure . f $ lookupStorage slot _storage 

  Surface slot f -> pure . f $ lookupNode slot _renderTree 

  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot i e' a -> case slot of 
    SlotBox -> do 
      e <- liftIO $ new_ e' 
      lift (renderE e) >>= \x@(MkRenderLeaf su cs) -> do
          ST.modify' $ \_ -> withDict (deriveStoreHas slot)
            ExEvalState $ EvalState {_storage =  modifyStorage slot (\(MkStorageBox m) -> 
                                                      MkStorageBox  $ M.insert (Indexed Index i) e m) _storage
                                    ,_renderTree = modifyNode slot (insertSurface i x) _renderTree 
                                    ,..} 
          pure a 
  
  Delete slot i a -> case slot of 
    SlotBox -> do 
      ST.modify' $ \_ -> 
        ExEvalState $ EvalState {_storage = modifyStorage slot (\(MkStorageBox  m) -> MkStorageBox $ M.delete (Indexed Index i) m) _storage
                                ,_renderTree = modifyNode slot (deleteSurface i) _renderTree
                                ,..}
      pure a 

  Render slot i f -> case slot of 
    SlotBox -> do
      let MkStorageBox  oldStorage = lookupStorage slot _storage  
      -- let oldSlot    = _storage    .! l
      case M.lookup (Indexed Index i) oldStorage of 
        Nothing -> pure $ f Nothing 
        Just e  -> do 
          lift (renderE e) >>= \r -> do 
              ST.modify' $ \_ -> 
                ExEvalState $ EvalState {_renderTree = modifyNode slot (\(MkRenderNode  m) -> 
                                                          MkRenderNode $ M.insert (Indexed Index i) r m) _renderTree
                                        ,..}
              pure $ f (Just r)  

-- | Deletes a child entity (and its rendered output in the renderTree).
--   
--   Requires a type application for the label 
delete :: forall label slots state i su cs q query 
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => i 
     -> EntityM slots state query IO ()
delete i = EntityM . liftF $ Delete (SlotBox :: SlotBox label slots '(i,su,RenderTree cs,q)) i () 

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.
create :: forall label slots i su cs q state query 
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => i
     -> Prototype su cs q
     -> EntityM slots state query IO ()
create i p = EntityM . liftF $ Create (SlotBox :: SlotBox label slots '(i,su,RenderTree cs,q))  i p ()

-- internal, don't export
renderChild :: forall label slots i su cs q state query 
             . ChildC label slots '(i,su,RenderTree cs,q)
     => i
     -> EntityM slots state query IO (Maybe (RenderLeaf '(i,su,RenderTree cs,q)))
renderChild i = EntityM . liftF $ Render (SlotBox :: SlotBox label slots '(i,su,RenderTree cs,q)) i id

deriveStoreHas :: forall label slots slot
                . SlotBox label slots slot 
               -> Dict (HasType label (StorageBox slot) (R.Map StorageBox slots))
deriveStoreHas SlotBox 
  = withDict 
    (mapDict weaken1 $ mapDict (mapHas @StorageBox @label @slot @slots) (Dict @((slots .! label) ~ slot)))  
    Dict 

lookupStorage :: forall label slots slot 
               . SlotBox label slots slot 
              -> Rec (R.Map StorageBox slots)
              -> StorageBox slot 
lookupStorage key@SlotBox storage = withDict (deriveStoreHas key) $ storage .! (Label @label)

deriveSurfaceHas :: forall label slots slot
                  . SlotBox label slots slot 
                 -> Dict (HasType label (RenderNode slot) (R.Map RenderNode slots))
deriveSurfaceHas SlotBox 
  = withDict 
    (mapDict weaken1 $ mapDict (mapHas @RenderNode @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict 

lookupNode :: forall label slots slot 
               . SlotBox label slots slot 
              -> RenderTree slots 
              -> RenderNode slot 
lookupNode key@SlotBox (MkRenderTree renderTree) 
  = withDict (deriveSurfaceHas key) 
  $ renderTree .! (Label @label)  

modifyNode :: forall label slots slot 
               . SlotBox label slots slot 
              -> (RenderNode slot -> RenderNode slot)
              -> RenderTree slots 
              -> RenderTree slots 
modifyNode key@SlotBox f tree@(MkRenderTree  renderTree)
  =  withDict (deriveSurfaceHas key) 
  $ case lookupNode key tree of 
      oldNode -> let newNode = f oldNode 
                     newTree = R.update (Label @label) newNode renderTree 
                 in MkRenderTree  newTree 

insertSurface :: forall i su cs q 
               . Ord i 
              => i 
              -> RenderLeaf '(i,su,RenderTree cs,q)
              -> RenderNode '(i,su,RenderTree cs,q)
              -> RenderNode '(i,su,RenderTree cs,q)
insertSurface i leaf@(MkRenderLeaf s r) (MkRenderNode  m)
  = MkRenderNode $ M.insert (Indexed Index i) leaf m

deleteSurface :: forall i su cs q 
               . Ord i 
              => i 
              -> RenderNode '(i,su,RenderTree cs,q)
              -> RenderNode '(i,su,RenderTree cs,q)
deleteSurface i (MkRenderNode  m) 
  = MkRenderNode $ M.delete (Indexed Index i) m  

modifyStorage :: forall label slots slot 
               . SlotBox label slots slot 
              -> (StorageBox slot -> StorageBox slot)
              -> Rec (R.Map StorageBox slots)
              -> Rec (R.Map StorageBox slots)
modifyStorage key@SlotBox f storage 
  = withDict (deriveStoreHas key) 
  $ R.update (Label @label) (f $ storage .! (Label @label)) storage 


mkProxy :: (AllUniqueLabels slots
           ,AllUniqueLabels (R.Map Proxy slots) 
           ,Forall (R.Map Proxy slots) Default)
        => Proxy (slots :: Row SlotData) 
        -> Rec (R.Map Proxy slots)
mkProxy Proxy = R.default' @Default def  

type TestRow = "slot1" .== Slot Int String Empty Maybe 
            .+ "slot2" .== Slot String Int Empty Maybe 

instance Default (Proxy (a :: k)) where 
  def = Proxy 

type ProxyC :: (k -> Constraint) -> Type -> Constraint 
type family ProxyC c t where 
  ProxyC (c :: k -> Constraint) (Proxy (a :: k)) = c a  

toStorage :: forall slots. (Forall slots SlotOrdC)
          => Proxy slots 
          -> Rec (R.Map Proxy slots)
          -> Rec (R.Map StorageBox slots)
toStorage proxy = R.transform @SlotOrdC @slots @Proxy @StorageBox go  
  where 
    go :: forall slot
        . Proxy slot
       -> StorageBox slot
    go proxy' =  MkStorageBox M.empty 

newtype IONode (slot :: SlotData) = IONode {ioNode :: IO (RenderNode slot)}



type Top :: k -> Constraint 
class Top k 
instance Top k 

toSurface :: forall slots. (Forall slots SlotOrdC)
          => Proxy slots 
          -> Rec (R.Map StorageBox slots)
          -> IO (Rec (R.Map RenderNode slots))
toSurface proxy r = R.traverseMap @SlotOrdC @IO @StorageBox @RenderNode @slots go r 
  where 
    go :: forall slot 
        . SlotOrdC slot 
       => StorageBox slot 
       -> IO (RenderNode slot)
    go box = toRenderNode' box  

visibly :: forall (k :: SlotData) (c :: SlotData -> Type) (d :: SlotData -> Type) 
         . SlotOrdC k 
        => (forall i s cs q. c (Slot i s cs q) -> d (Slot i s cs q)) 
        -> c k 
        -> d k  
visibly f =  unsafeCoerce f

toRenderNode' :: forall slot. SlotOrdC slot =>  StorageBox slot -> IO (RenderNode slot)
toRenderNode' box@(MkStorageBox m) = ioNode $ visibly toRenderNode box 

toRenderNode ::  StorageBox '(i,su,RenderTree cs,q) 
             -> IONode '(i,su,RenderTree cs,q)
toRenderNode (MkStorageBox  m) = IONode $ do 
  rm <- traverse renderE m 
  pure $ MkRenderNode rm 

bop :: Rec
  ('R
     '[ "slot1" ':-> StorageBox '(Int, String, RenderTree Empty, Maybe),
        "slot2" ':-> StorageBox '(String, Int, RenderTree Empty, Maybe)])
bop = mkStorage (Proxy @TestRow)


bebop :: IO
  (Rec
     ('R
        '[ "slot1" ':-> RenderNode '(Int, String, RenderTree Empty, Maybe),
           "slot2" ':-> RenderNode '(String, Int, RenderTree Empty, Maybe)]))
bebop = toSurface (Proxy @TestRow) bop  

{--            
mkNodes :: (SlotOrdC slots 
           ,AllUniqueLabels slots 
           ,AllUniqueLabels (RProxy (slots :: Row SlotData)
        -> 
--}
-- | Constructs an empty slot storage record.


mkStorage :: (AllUniqueLabels slots, AllUniqueLabels (Map Proxy slots),
 Forall slots SlotOrdC, Forall (Map Proxy slots) Default) =>
 Proxy slots -> Rec (Map StorageBox slots)
mkStorage proxy = toStorage proxy $ mkProxy  proxy 

