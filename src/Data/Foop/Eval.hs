{-# LANGUAGE RecordWildCards #-}
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

-- | Extracts a label `l` from a `SlotBox l slots q i r`
slotLabel :: forall slots q i r l. SlotBox l slots q i r -> Label l 
slotLabel SlotBox = Label @l

-- | Existenial eliminator for an ExEvalState 
withExEval :: forall query surface  r 
            . ExEvalState surface query 
            -> (forall slots state. EvalState slots surface state query -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

-- | Constructs an entity from a prototype
new_ :: forall surface query 
        . Prototype surface query 
       -> IO (Entity surface query)  
new_ (Prototype espec@MkSpec{..}) = newTVarIO e' >>= \eStore -> pure $  Entity eStore 
  where 
    !evalSt = initE espec 

    !e' = mkEntity_ evalSt 

-- | Initializes an EvalState given a Spec 
initE :: SlotConstraint slots 
      => Spec slots r  st q 
      -> EvalState slots r st q 
initE espec@MkSpec{..} 
  = EvalState {_entity     = espec 
              ,_state      = initialState 
              ,_storage    = mkStorage slots
              ,_renderTree = mkRenderTree slots}  

-- | Constructs and EntityStore from an EvalState 
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
-- | Runs an entity. For internal use only; you should use `tell` and `request` instead of this. 
run :: forall x q r. q x -> Entity r q -> IO x
run i (Entity tv) = do
  e <- readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  atomically $ writeTVar tv newObj -- write new store thingy to tvar 
  pure x 

-- internal, don't export
-- | Retrieves the map of the entity's children. For internal use.
getSlot :: forall l i  r q q' slots st
         . (ChildC l i r q' slots) 
        => EntityM slots st q IO (M.Map i (Entity r q'))
getSlot = EntityM . liftF $ Child (SlotBox :: SlotBox l slots q' i r) id 

-- don't export 
-- | `getSlot` but with a SlotBox (which serves as a dictionary for ChildC) instead of the ChildC constraint 
getSlot' ::  SlotBox l slots q i r
         -> EntityM slots  state query IO (M.Map i (Entity r q))
getSlot' slot = EntityM . liftF $ Child slot id 

-- don't export 
-- | Like `getSlot` but for the rendered surface 
getSurface :: forall l i r q q' m' slots st 
            . (ChildC l i r q' slots, Functor m', MonadIO m')
           => EntityM slots st q m' (M.Map i r)
getSurface = EntityM . liftF $ Surface (SlotBox :: SlotBox l slots q' i r) id 

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
tell :: forall lbl i r q' q slots state
      . (ChildC lbl i r q' slots, Ord i)
     => i 
     -> Tell q' 
     -> EntityM slots state q IO ()
tell i q = do 
  mySlot <- getSlot @lbl
  case M.lookup i mySlot of  
    Nothing -> pure () 
    Just e  -> do 
      lift (run (mkTell q) e)
      _ <- renderChild @lbl i
      pure ()

-- | `tellAll q` executes a tell query for every child entity at a given slot. 
--   
--    Like `tell`, this requires a type application for the child label. 
-- 
--    E.g. `tell @"childLabel" MyQuery` 
tellAll :: forall lbl i r q' q slots state context
      . (ChildC lbl i r q' slots, Ord i)
     => Tell q' 
     -> EntityM slots state q IO () 
tellAll q = do 
  mySlot <- M.keys <$> getSlot @lbl 
  mapM_ (\i -> tell @lbl i q) mySlot

-- | `request i q` takes an index/key for a child entity and a data constructor of 
--   that entity's algebra, and returns a monadic action in the parent entity which executes the 
--   query and returns (Maybe) the result of the query. 
--
--   Like `tell`, this requires a type application for the child label. 
--   
--   e.g. `request @"childLabel" 123 MyQuery`   
request :: forall lbl i r q' q slots state context x
      . (ChildC lbl i r q' slots, Ord i)
     => i 
     -> Request q' x  
     -> EntityM slots state q IO (Maybe x)
request i q = do 
  mySlot <- getSlot @lbl  
  case M.lookup i mySlot of 
    Nothing -> pure Nothing 
    Just e  -> do 
      o <- lift (run (mkRequest q) e)
      _ <- renderChild @lbl i 
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall lbl i r q' q slots state context x
      . (ChildC lbl i r q' slots, Ord i)
     => Request q' x  
     -> EntityM slots state q IO [x]
requestAll q = do 
  mySlot <- M.keys <$> getSlot @lbl 
  catMaybes <$> mapM (\i -> request @lbl i q) mySlot 

mkRequest :: Request q x -> q x
mkRequest q = q id 

-- | Given an Entity, renders its surface
renderE :: Entity surface query -> IO surface
renderE (Entity tv) = do 
  e <- readTVarIO tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> do 
      let surface = render (renderer  _entity) _state 
      onRender (renderer _entity) surface 
      pure surface 

evalF :: forall slots' r' st' q' a' 
    .  EvalState slots' r' st' q'
    -> EntityF slots' st' q' IO a'
    -> ST.StateT (ExEvalState r' q') IO a' 
evalF EvalState{..} = \case 

  State f -> case f _state of 
    (a,newState) -> do 
        let newSurface = render (renderer _entity) newState 
        liftIO $ onRender (renderer _entity) newSurface 
        ST.modify' $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Query q -> case apNT (handleQuery _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  

  Child slot f -> case slot of -- need this for type inference, it's not superfluous here 
    SlotBox -> pure . f $ _storage .! slotLabel slot

  Surface slot f -> case slot of 
    SlotBox -> pure . f $ _renderTree .! slotLabel slot 

  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot i e' a -> case slot of 
    SlotBox -> do 
      e <- liftIO $ new_ e' 
      lift (renderE e) >>= \x -> do
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
      let newSurface = M.insert i oldSurface 
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
delete :: forall lbl i r q'  q slots state 
      . (ChildC lbl i r q' slots, Ord i)
     => i 
     -> EntityM slots state q IO ()
delete i = EntityM . liftF $ Delete (SlotBox :: SlotBox lbl slots q' i r) i () 

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.
create :: forall lbl i r q' q slots state
      . (ChildC lbl i r q' slots, Ord i, SlotConstraint slots)
     => i
     -> Prototype r q' 
     -> EntityM slots state q IO ()
create i p = EntityM . liftF $ Create (SlotBox :: SlotBox lbl slots q' i r) i p ()

-- internal, don't export
renderChild :: forall lbl i r q' q slots state m  
      . (ChildC lbl i r q' slots, Ord i, Functor m)
     => i
     -> EntityM slots state q m (Maybe r)
renderChild i = EntityM . liftF $ Render (SlotBox :: SlotBox lbl slots q' i r) i id

