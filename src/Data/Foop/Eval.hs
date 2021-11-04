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
new_ :: forall surface slots query 
        . Prototype surface slots query 
       -> IO (Entity surface slots query)  
new_ (Prototype espec@MkSpec{..}) = newTVarIO e' >>= \eStore -> pure $  Entity eStore 
  where 
    !evalSt = initE espec 

    !e' = mkEntity_ evalSt 

-- | Initializes an EvalState given a Spec 
initE ::  Spec slots r st q 
      -> EvalState slots r st q 
initE espec@MkSpec{..} 
  = EvalState {_entity     = espec 
              ,_state      = initialState 
              ,_storage    = mkStorage slots
              ,_renderTree = mkRenderTree slots}  

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
run :: forall x q s r. q x -> Entity r s q -> IO x
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
getSlot = EntityM . liftF $ Child (SlotBox :: SlotBox label slots slot)  id 

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
tell_ :: forall label slots i su cs q state query 
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Indexed '(i,su,RenderTree cs,q)
     -> Tell q
     -> EntityM slots state query IO ()
tell_ i q = do 
  MkStorageBox proxy mySlot <- getSlot @label
  case M.lookup  i mySlot of  
    Nothing -> pure () 
    Just e  -> do 
      lift (run (mkTell q) e)
      _ <- renderChild @label i
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
  MkStorageBox proxy mySlot <- getSlot @label @slots @'(i,su,RenderTree cs,q)
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
request_ :: forall label i su cs q slots state query x
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Indexed '(i,su,RenderTree cs,q)
     -> Request q x  
     -> EntityM slots state query IO (Maybe x)
request_ i q = do 
  MkStorageBox proxy mySlot <- getSlot @label 
  case M.lookup i mySlot of 
    Nothing -> pure Nothing 
    Just e  -> do 
      o <- lift (run (mkRequest q) e)
      _ <- renderChild @label i 
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall label i su cs q slots state query x
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => Request q x  
     -> EntityM slots state query IO [x]
requestAll q = do 
  MkStorageBox proxy mySlot <- getSlot @label
  let slotKeys = M.keys mySlot 
  catMaybes <$> mapM (\i -> request_ @label i q) slotKeys 

mkRequest :: Request q x -> q x
mkRequest q = q id 

-- | Given an Entity, renders its surface. Doesn't update anything, but does run the IO action.
renderE :: forall index surface children query. Entity surface children query -> IO (RenderNode '(index,surface,RenderTree children,query))
renderE (Entity tv) = do 
  e <- readTVarIO tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> do 
      let surface = render (renderer  _entity) _renderTree _state 
      onRender (renderer _entity) surface 
      pure $  MkRenderNode Proxy $ #surface  .== surface 
                               .+  #children .== _renderTree

evalF :: forall slots' r' st' q' a' 
    .  EvalState slots' r' st' q'
    -> EntityF slots' st' q' IO a'
    -> ST.StateT (ExEvalState r' slots' q') IO a' 
evalF EvalState{..} = \case 

  State f -> case f _state of 
    (a,newState) -> do 
        let newSurface = render (renderer _entity) _renderTree newState 
        liftIO $ onRender (renderer _entity) newSurface 
        ST.modify' $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Query q -> case apNT (handleQuery _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  

  Child slot f ->  pure . f $ lookupStorage slot _storage 

  Surface slot f -> pure . f $ lookupSurface slot _renderTree 

  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot i e' a -> case slot of 
    SlotBox -> do 
      e <- liftIO $ new_ e' 
      lift (renderE e) >>= \x -> do
          let MkRenderNode proxy1 oldNode = lookupSurface slot _renderTree 
          let MkStorageBox proxy2 oldSlot    = lookupStorage slot _storage    
          let newSlot    = MkStorageBox proxy1 $ M.insert (Indexed Index i) e oldSlot
          let newSurface = modifySurface slot  (over #children M.insert (Indexed Index i) x)
          ST.modify' $ \_ -> withDict (deriveStoreHas slot)
            ExEvalState $ EvalState {_storage =  modifyStorage slot (const newSlot) _storage
                                    ,_renderTree = R.update l newSurface _renderTree
                                    ,..} 
          pure a 
  
  Delete slot i a -> case slot of 
    SlotBox -> do 
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

  Render slot i f -> case slot of 
    SlotBox -> do
      let l = slotLabel slot 
      let oldSurface = _renderTree .! l
      let oldSlot    = _storage    .! l
      case M.lookup i oldSlot of 
        Nothing -> pure $ f Nothing 
        Just e  -> do 
          lift (renderE e) >>= \r -> do 
              let newSurface = M.insert i r oldSurface 
              ST.modify' $ \_ -> 
                ExEvalState $ EvalState {_renderTree = R.update l newSurface _renderTree
                                        ,..}
              pure $ f (Just r)  


-- | Deletes a child entity (and its rendered output in the renderTree).
--   
--   Requires a type application for the label 
delete :: forall label slots state i su cs q query 
      . (ChildC label slots '(i,su,cs,q))
     => i 
     -> EntityM slots state query IO ()
delete i = EntityM . liftF $ Delete SlotBox (Indexed Index i) () 

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.
create :: forall label slots i su cs q state query 
      . (ChildC label slots '(i,su,RenderTree cs,q))
     => i
     -> Prototype su cs q
     -> EntityM slots state query IO ()
create i p = EntityM . liftF $ Create SlotBox  i p ()

-- internal, don't export
renderChild :: forall label slots i su cs q state query 
             . ChildC label slots '(i,su,RenderTree cs,q)
     => Indexed '(i,su,RenderTree cs,q) 
     -> EntityM slots state query IO (Maybe (RenderNode '(i,su,RenderTree cs,q)))
renderChild i = EntityM . liftF $ Render SlotBox i id

{--
storeHas :: forall (l :: Symbol)
                   (slots :: Row SlotData)
                   (slot :: SlotData)
          . HasType l slot slots :- HasType l (StorageBox slot) (R.Map StorageBox slots)
storeHas = Sub $ unsafeCoerce $ Dict @(HasType l slot slots)
--}
deriveStoreHas :: forall label slots slot. SlotBox label slots slot 
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

lookupSurface :: forall label slots slot 
               . SlotBox label slots slot 
              -> RenderTree slots 
              -> RenderNode slot 
lookupSurface key@SlotBox (MkRenderTree proxy renderTree) = withDict (deriveSurfaceHas key) $ renderTree .! (Label @label)  

modifySurface :: forall label slots slot 
               . SlotBox label slots slot 
              -> (RenderNode slot -> RenderNode slot)
              -> RenderTree slots 
              -> RenderTree slots 
modifySurface key@SlotBox f (MkRenderTree proxy renderTree)
  =  withDict (deriveStoreHas key) 
  $ case renderTree .! #children of 
      nodes -> MkRenderTree proxy $ R.update (Label @label) (set #children (f $ view #children renderTree)) renderTree

modifyStorage :: forall label slots slot 
               . SlotBox label slots slot 
              -> (StorageBox slot -> StorageBox slot)
              -> Rec (R.Map StorageBox slots)
              -> Rec (R.Map StorageBox slots)
modifyStorage key@SlotBox f storage 
  = withDict (deriveStoreHas key) 
  $ R.update (Label @label) (f $ storage .! (Label @label)) storage 


surfaceHas :: forall (l :: Symbol)
                     (i :: Type)
                     (su :: Type) 
                     (cs :: Row SlotData)
                     (q :: Type -> Type)
                     (slots :: Row SlotData)
            . HasType l (Slot i su cs q) slots :- HasType l (RenderNode (Slot i su cs q)) (R.Map RenderNode slots)
surfaceHas  = Sub $ unsafeCoerce $ Dict @(HasType l (Slot i su cs q) slots)
--}




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
        . SlotOrdC slot
       => Proxy slot
       -> StorageBox slot
    go proxy' =  MkStorageBox proxy' M.empty 

newtype IONode (slot :: SlotData) = IONode (IO (RenderNode slot))

toSurface :: forall slots. (Forall slots SlotOrdC)
          => Proxy slots 
          -> Rec (R.Map StorageBox slots)
          -> Rec (R.Map RenderNode slots)
toSurface proxy = R.transform @SlotOrdC @slots @Proxy @RenderNode go 
  where 
    go :: forall slot 
        . SlotOrdC slot 
       => StorageBox slot 
       -> IONode slot 
    go = undefined 

bop = mkStorage (Proxy @TestRow)

{--            
mkNodes :: (SlotOrdC slots 
           ,AllUniqueLabels slots 
           ,AllUniqueLabels (RProxy (slots :: Row SlotData)
        -> 
--}
-- | Constructs an empty slot storage record.


mkStorage proxy = toStorage proxy $ mkProxy  proxy 

-- | Constructs an empty render tree.
mkRenderTree :: forall slots 
              . -- SlotConstraint slots => 
              Proxy slots -> RenderTree slots 
mkRenderTree proxy = undefined --  R.default' @Default def 