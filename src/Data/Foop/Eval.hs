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

import GHC.TypeLits (Symbol)
import qualified Data.Constraint.Forall as DC
import Data.Foop.Slot

import Data.Functor 
import Data.Foop.Paths 
import Data.Foop.Exists


-- | Extracts a label `l` from a `SlotKey l slots q i r`
slotLabel :: forall l slots slot . SlotKey l slots slot -> Label l
slotLabel SlotKey = Label @l

-- | Existenial eliminator for an ExEvalState 
withExEval :: forall deps roots shoots surface query  r
            . ExEvalState deps roots shoots surface query 
            -> (forall state. EvalState deps roots shoots surface state query -> r)
            -> r
withExEval (ExEvalState e) f = f e

-- | Constructs an entity from a model
new_ :: forall index surface slots query context deps loc 
        . ( Ord index
          , Forall slots SlotOrdC
          ) => Segment' loc 
            -> RootOf loc
            -> Model loc deps (Slot index surface slots query) 
            -> IO (Entity (Slot index surface slots query))
new_ path tmv (Model spec@(MkSpec iState qHandler renderR slots _)) = do 
  let eState = initE path tmv spec 
  e <- newTVarIO $ mkEntity_ @index eState 
  pure $ Entity e 

{-- 
  espec -> do
    let evalSt = initE cxt espec
    eStore <- newTVarIO $  mkEntity_ evalSt
    pure $  Entity eStore
--}
-- | Constructs an entity from a model
new_' :: forall roots shoots query surface i state deps 
        . ( Forall shoots SlotOrdC
          , AllExtend ('Begin :> 'Start (Slot () surface roots query)) deps 
          , SlotConstraint shoots
          )
       => Spec ('Begin :> 'Start (Slot () surface roots query)) deps shoots state (Slot () surface roots query)  
       -> EBranch shoots  
       -> surface 
       -> ETree roots  
       -> IO (Entity (Slot () surface roots query))
new_' spec@MkSpec{..} storage surface tree   =  do

    env :: TMVar (Entity (Slot () surface roots query)) <- newEmptyTMVarIO

    Handler h     <- pure handleQuery 
    MkPaths deps  <- pure $ pos h 

    let here = Here :: Segment 'Begin ('Begin :> 'Start (Slot () surface roots query))

    let evalSt = EvalState {_entity      = spec 
                           ,_state       = initialState 
                           ,_shoots      = storage 
                           ,_surface     = surface 
                           ,_roots       = tree 
                           ,_environment = atlas @('Begin :> 'Start (Slot () surface roots query)) (RootOf env) here deps
                            }
    eStore <- newTVarIO $  mkEntity_ @() evalSt
    atomically $ putTMVar env (Entity eStore)

    pure $  Entity eStore

mkRoots :: forall roots models parent  
         . ( roots ~ UnModel models
           , AllCompatibleModels parent models 
           ) => RootOf parent 
             -> Segment' parent 
             -> Rec models 
             -> IO (ETree roots)
mkRoots rootOf path models = ETree <$> R.traverse ( rootOf path models  

-- | Initializes an EvalState given a Spec 
initE :: forall loc slots surface st q deps roots shoots i
       . ( SlotConstraint slots)
      => Segment' loc
      -> RootOf loc 
      -> Spec loc deps shoots st (Slot i surface roots q)
      -> EvalState deps roots shoots surface st q 
initE path tmv espec@MkSpec{..}
  = EvalState {_entity      = espec
              ,_state       = initialState
              ,_shoots      = mkShoots shoots  
              ,_surface     = render renderer initialState
              ,_roots       = mkRoots @roots roots 
              ,_environment = tmv 
              }

-- | Constructs and EntityStore from an EvalState 
mkEntity_ :: forall i slots surface  st query roots shoots deps
           . (Ord i)
          => EvalState deps roots shoots surface st query 
          -> EntityStore deps roots shoots surface query 
mkEntity_ e@EvalState{..} = store go (ExEvalState e)
  where
    go :: ExEvalState deps roots shoots surface query  
       -> Transformer deps roots shoots surface query  
    go ex@(ExEvalState est@(EvalState entity@(MkSpec iState (Handler hQuery) rendr proxy _) sta str su loc env)) 
      = Transformer $ \qx -> 
          case apNT (extract hQuery) (Q . liftCoyoneda $ qx)  of 
            EntityM m -> do  
              let st = foldF (evalF  (EvalState entity sta str su loc env)) m
              ST.runStateT st ex
--}
-- don't export this
-- | Runs an entity. For internal use only; you should use `tell` and `request` instead of this. 
run :: forall i su cs q x. Ord i => q x -> Entity (Slot i su cs q) -> IO x
run i (Entity tv) = do
  e <- readTVarIO tv  -- reads the store from the tvar 
  Transformer f <- pure $ extract e 
  (x,st) <- f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ @i x  -- recreate the store comonad thingy from the new state 
  atomically $ writeTVar tv newObj -- write new store thingy to tvar 
  pure x

-- internal, don't export
-- | Retrieves the map of the entity's children. For internal use.
getSlot :: forall  label roots shoots slot st q deps 
         . (ChildC label shoots slot, SlotConstraint shoots)
        => EntityM deps roots shoots st q IO (StorageBox slot)
getSlot = EntityM . liftF $ GetSlot (SlotKey :: SlotKey label slots slot) id

-- don't export 
-- | `getSlot` but with a SlotKey (which serves as a dictionary for ChildC) instead of the ChildC constraint 
getSlot' ::  SlotKey label shoots slot
         -> EntityM deps roots shoots state query IO (StorageBox slot)
getSlot' slot = EntityM . liftF $ GetSlot slot id

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
tell :: forall label shoots roots  i su cs q state query deps  
      . (ChildC label shoots (Slot i su cs q), SlotConstraint shoots)
     => i
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
tell i = tell_ @label (Indexed Index i)

tell_ :: forall label shoots roots  i su cs q state query deps  
      . (ChildC label shoots (Slot i su cs q), SlotConstraint shoots)
     => Indexed (Slot i su cs q)
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
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
tellAll :: forall label shoots roots  i su cs q state query deps  
      . (ChildC label shoots (Slot i su cs q), SlotConstraint shoots)
     => i
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
tellAll q = do
  MkStorageBox mySlot <- getSlot @label @shoots @(Slot i su cs q)
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
request :: forall label i su cs q roots shoots state query x deps  
      . (ChildC label shoots (Slot i su cs q), SlotConstraint shoots)
     => i
     -> Request q x
     -> EntityM deps roots shoots state query IO (Maybe x)
request i = request_ @label (Indexed Index i)

request_ :: forall label i su cs q roots shoots state query x deps 
      . (ChildC label shoots (Slot i su cs q), SlotConstraint shoots)
     => Indexed (Slot i su cs q)
     -> Request q x
     -> EntityM deps roots shoots state query IO (Maybe x)
request_ i q = do
  MkStorageBox mySlot <- getSlot @label
  case M.lookup i mySlot of
    Nothing -> pure Nothing
    Just e  -> do
      o <- lift (run (mkRequest q) e)
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall label i su cs q roots shoots state query deps x 
      . (ChildC label shoots (Slot i su cs q), SlotConstraint shoots)
     => Request q x
     -> EntityM deps roots shoots state query IO [x]
requestAll q = do
  MkStorageBox mySlot <- getSlot @label
  let slotKeys = M.keys mySlot
  catMaybes <$> mapM (\i -> request_ @label i q) slotKeys

mkRequest :: Request q x -> q x
mkRequest q = q id

evalF :: forall  roots shoots surface state query root deps a
    .  EvalState  deps roots shoots surface state query
    -> EntityF deps roots shoots state query IO a
    -> ST.StateT (ExEvalState deps roots shoots surface query) IO a
evalF eState@EvalState{..} = \case

  State f -> case f _state of
    (a,newState) -> do
        newSurface <- renderS newState
        ST.modify' $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a

--  Observe _ _ -> undefined 

  Interact _ _ -> undefined 

  Lift ma -> lift ma
{--
  Context g -> 
    unboxContext' _context $ \d tv -> do 
      leaf <- liftIO (readTVarIO tv)
      pure $ withDict d (leaf ^. g)
--}
  Query q -> case _entity of 
    MkSpec iState (Handler hQuery) renderR a b  -> 
      case apNT (extract hQuery) (Q q) of
        EntityM ef -> foldF (evalF (EvalState {..})) ef

  GetShoot slot f ->  pure . f $ lookupStorage slot _storage

  GetRoot _ _ -> undefined 

  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot l i e' a -> case slot of
    SlotKey -> undefined {-- 
                do
      e <- liftIO $ new_ (_location ) _environment e' 
      lift (atomically $ observeE e) >>= \x@(MkRenderLeaf su cs) -> do
          ST.modify' $ \_ -> withDict (deriveStoreHas slot)
            ExEvalState $ EvalState {_storage =  modifyStorage slot (\(MkStorageBox m) ->
                                                      MkStorageBox  $ M.insert (Indexed Index i) e m) _storage
                                    ,..}
          pure a
--}
  Delete slot i a -> undefined {-- 
  case slot of
    SlotKey -> do
      ST.modify' $ \_ ->
        ExEvalState $ EvalState {_storage = modifyStorage slot (\(MkStorageBox  m) -> MkStorageBox $ M.delete (Indexed Index i) m) _storage
                                ,..}
      pure a --}
 where
   renderS :: MonadIO n => state -> n surface
   renderS st = do
     let newSurface = render (renderer _entity)  st
     liftIO $ onRender (renderer _entity) newSurface
     pure newSurface

-- | Deletes a child entity (and its rendered output in the renderTree).
--   
--   Requires a type application for the label 
delete :: forall label roots shoots state i su cs q query deps
      . (ChildC label shoots (Slot i su cs q), Forall shoots SlotOrdC)
     => i
     -> EntityM deps roots shoots state query IO ()
delete i = EntityM . liftF $ Delete (SlotKey :: SlotKey label slots (Slot i su cs q)) i ()

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.

create :: forall l i cs su q deps slot state query roots shoots  ds loc
        . (Ord i
        , Forall shoots SlotOrdC, Forall cs SlotOrdC
        , KnownSymbol l
        , HasType l (Slot i su cs q) shoots) 
       => i
       -> Model loc ds (Slot i su cs q)
       -> EntityM deps roots shoots state query IO ()
create  i p = EntityM . liftF $ Create (SlotKey @l ) Label i p ()

{--
observe_ :: forall l m deps a slots state query path 
          . (Functor m, KnownSymbol l, HasType l (Segment 'Begin path) deps) 
         => Label l
         -> (RenderLeaf (EndOf path) -> a) 
         -> EntityM deps slots state query m a
observe_ path f = EntityM . liftF $ Observe path f 
--}