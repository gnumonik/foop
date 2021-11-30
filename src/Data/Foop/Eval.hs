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
import Data.Type.Equality
import Data.Functor.Compose 
import Data.Foop.Dictionary (deriveHas')
import Data.Constraint

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
new_ :: forall index surface roots query shoots context deps source state 
        .      TMVar (Entity source)
            -> Spec source deps shoots state (Slot index surface roots query) 
            -> STM (Entity (Slot index surface roots query))
new_ tmv spec@(MkSpec iState qHandler renderR shoots roots deps) = do 
  eState <- initE tmv spec 
  e <- newTVar $ mkEntity_ @index eState 
  pure $ Entity e 

-- | Constructs an entity from a model
new_' :: forall roots shoots query surface i state deps 
        . Spec (Slot () surface roots query) deps shoots state (Slot () surface roots query)  
       -> surface 
       -> IO (Entity (Slot () surface roots query))
new_' spec@MkSpec{..}  surface  =  do

    env :: TMVar (Entity (Slot () surface roots query)) <- newEmptyTMVarIO

    rs' <- pure $ assemble1 env roots 

    rs''  <- assemble2 rs' 

    Handler h     <- pure handleQuery 
    deps  <- pure $ compat @(Slot () surface roots query) @deps env 

    let here = Here :: Segment 'Begin ('Begin :> 'Start (Slot () surface roots query))

    let evalSt = EvalState {_entity      = spec 
                           ,_state       = initialState 
                           ,_shoots      = mkStorage shoots 
                           ,_surface     = surface 
                           ,_roots       = ETree rs''
                           ,_environment = deps
                            }
    eStore <- newTVarIO $ mkEntity_ @() evalSt
    atomically $ putTMVar env (Entity eStore)

    pure $  Entity eStore

 where 
  assemble2 :: Rec (R.Map STMNode roots) -> IO (Rec (R.Map ENode roots))
  assemble2 rx = R.traverseMap @(SlotI Ord) @IO @STMNode @ENode @roots go rx 
   where 
     go :: forall x. STMNode x -> IO (ENode x)
     go (STMNode mx) = atomically mx 

  assemble1 :: TMVar (Entity (Slot () surface roots query))
            -> Models (Slot () surface roots query) roots
            -> Rec (R.Map STMNode roots)
  assemble1 tmv (MkModels ms) = R.transform
                                  @(SlotI Ord)
                                  @roots 
                                  @(Model (Slot () surface roots query))
                                  @STMNode 
                                  go ms 
   where 
    go :: forall slot
        . SlotI Ord slot 
      => Model (Slot () surface roots query) slot 
      -> STMNode slot 
    go (Model spec@MkSpec{..}) = STMNode $ do 
      e <- new_ tmv spec 
      pure . ENode $ e 
      
peekSurface :: Entity (Slot i su rs q) -> STM su 
peekSurface (Entity e) = readTVar e >>= \t -> case pos t of 
  ExEvalState (EvalState _ _ _ _ surface _) -> pure surface  
  
  

mkRoots :: TMVar (Entity source)
        -> Models source models 
        -> STM (ETree roots)
mkRoots path models = undefined -- ETree <$> R.traverse ( rootOf path models  

-- | Initializes an EvalState given a Spec 
initE :: forall source surface st q deps roots shoots i
       . TMVar (Entity source)
      -> Spec source deps shoots st (Slot i surface roots q)
      -> STM (EvalState deps roots shoots surface st q) 
initE  tmv espec@MkSpec{..} = do 
        rs            <- mkRoots tmv roots 
        Handler h     <- pure handleQuery 
        deps  <- pure $ compat @source @deps tmv 
        pure $ EvalState {_entity      = espec
              ,_state       = initialState
              ,_shoots      = undefined -- mkShoots shoots  
              ,_surface     = render renderer initialState
              ,_roots       = rs 
              ,_environment = deps 
              }

-- | Constructs and EntityStore from an EvalState 
mkEntity_ :: forall i slots surface  st query roots shoots deps
           . EvalState deps roots shoots surface st query 
          -> EntityStore deps roots shoots surface query 
mkEntity_ e@EvalState{..} = store go (ExEvalState e)
  where
    go :: ExEvalState deps roots shoots surface query  
       -> Transformer deps roots shoots surface query  
    go ex@(ExEvalState est@(EvalState entity@(MkSpec iState (Handler hQuery) rendr shoots roots deps) sta str su loc env)) 
      = Transformer $ \qx -> 
          case apNT (extract hQuery) (Q . liftCoyoneda $ qx)  of 
            EntityM m -> do  
              let st = foldF (evalF  (EvalState entity sta str su loc env)) m
              ST.runStateT st ex

-- don't export this
-- | Runs an entity. For internal use only; you should use `tell` and `request` instead of this. 
run :: forall i su cs q x. q x -> Entity (Slot i su cs q) -> IO x
run i (Entity tv) =  do
    e <- readTVarIO tv  -- reads the store from the tvar 
    Transformer f <- pure $ extract e 
    (x,st) <- f i -- apply the i-o transformer to some input 
    let newObj = withExEval st $ \x ->  mkEntity_ @i x  -- recreate the store comonad thingy from the new state 
    atomically $ writeTVar tv newObj -- write new store thingy to tvar 
    pure x

-- internal, don't export
-- | Retrieves the map of the entity's children. For internal use.
getShoot :: forall  label shoots slot roots st q deps 
         . (ChildC label shoots slot, SlotConstraint shoots)
        => EntityM deps roots shoots st q IO (ELeaf slot)
getShoot = EntityM . liftF $ GetShoot (SlotKey :: SlotKey label shoots slot) id

-- don't export 
-- | `getSlot` but with a SlotKey (which serves as a dictionary for ChildC) instead of the ChildC constraint 
getShoot' ::  SlotKey label shoots slot
         -> EntityM deps roots shoots state query IO (ELeaf slot)
getShoot' slot = EntityM . liftF $ GetShoot slot id

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
      . (ChildC label shoots (Slot i su cs q), Ord i, SlotConstraint shoots)
     => i
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
tell i = tell_ @label i

tell_ :: forall label shoots roots  i su cs q state query deps  
      . (ChildC label shoots (Slot i su cs q), Ord i, SlotConstraint shoots)
     => i
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
tell_ i q = do
  ELeaf mySlot <- getShoot @label
  case M.lookup  (Ix i) mySlot of
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
      . (ChildC label shoots (Slot i su cs q), Ord i, SlotConstraint shoots)
     =>  Tell q
     -> EntityM deps roots shoots state query IO ()
tellAll q = do
  ELeaf mySlot <- getShoot @label @shoots @(Slot i su cs q)
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
      . (ChildC label shoots (Slot i su cs q)
        , SlotConstraint shoots
        , Forall shoots (SlotI Ord)
        , Ord i)
     => i
     -> Request q x
     -> EntityM deps roots shoots state query IO (Maybe x)
request i = request_ @label  i

request_ :: forall label i su cs q roots shoots state query x deps 
      . (ChildC label shoots (Slot i su cs q)
        , SlotConstraint shoots
        , Forall shoots (SlotI Ord)
        , Ord i)
     => i
     -> Request q x
     -> EntityM deps roots shoots state query IO (Maybe x)
request_ i q = do
  ELeaf mySlot <- getShoot @label
  case M.lookup (Ix i) mySlot of
    Nothing -> pure Nothing
    Just e  -> do
      o <- lift (run (mkRequest q) e)
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall label i su cs q roots shoots state query deps x 
      . (ChildC label shoots (Slot i su cs q), Ord i, SlotConstraint shoots)
     => Request q x
     -> EntityM deps roots shoots state query IO [x]
requestAll q = do
  ELeaf mySlot <- getShoot @label
  let slotKeys = M.keys mySlot
  catMaybes <$> mapM (\(Ix i) -> request_ @label  i q) slotKeys

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


  Interact lbl f ->  goInteract lbl f -- pure . f $ _environment R..! lbl 

  Lift ma -> lift ma

  Query q -> case _entity of 
    MkSpec iState (Handler hQuery) renderR a b c -> 
      case apNT (extract hQuery) (Q q) of
        EntityM ef -> foldF (evalF (EvalState {..})) ef

  GetShoot key@SlotKey f ->  pure . f $ lookupLeaf key _shoots

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
   goInteract :: forall l slot 
               . (KnownSymbol l, HasType l slot deps)
              => Label l 
              -> (ENode slot -> STM a)
              -> ST.StateT (ExEvalState deps roots shoots surface query) IO a
   goInteract l f = case deriveHas' @STMNode @l @deps @slot of 
     d@Dict -> go d l f _environment  
    where 
      go :: Dict (HasType l (STMNode slot) (R.Map STMNode deps))
          -> Label l
          -> (ENode slot -> STM a)
          -> Rec (R.Map STMNode deps)
          -> ST.StateT (ExEvalState deps roots shoots surface query) IO a
      go d@Dict l' f' ds = case withDict d (ds R..! l') of 
        STMNode ex -> liftIO . atomically $ ex >>= f'  

   renderS :: MonadIO n => state -> n surface
   renderS st = do
     let newSurface = render (renderer _entity)  st
     liftIO $ onRender (renderer _entity) newSurface
     pure newSurface

-- | Deletes a child entity (and its rendered output in the renderTree).
--   
--   Requires a type application for the label 
delete :: forall label roots shoots state i su cs q query deps
      . (ChildC label shoots (Slot i su cs q), Forall shoots (SlotI Ord))
     => i
     -> EntityM deps roots shoots state query IO ()
delete i = EntityM . liftF $ Delete (SlotKey :: SlotKey label shoots (Slot i su cs q)) i ()

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.

create :: forall l i cs su q deps slot state query roots shoots  ds loc
        . (Ord i
        , Forall shoots (SlotI Ord), Forall cs (SlotI Ord)
        , KnownSymbol l
        , HasType l (Slot i su cs q) shoots) 
       => i
       -> Model loc (Slot i su cs q)
       -> EntityM deps roots shoots state query IO ()
create  i p = EntityM . liftF $ Create (SlotKey @l ) Label i p ()



observe :: forall l i su cs q deps roots shoots state query m a 
          . (Functor m
          , KnownSymbol l
          , HasType l (Slot i su cs q) deps) 
         => Label l 
         -> (su -> a) 
         -> EntityM deps roots shoots state query m a
observe l f = EntityM . liftF $ Interact l (\(ENode e) -> f <$> peekSurface e)
