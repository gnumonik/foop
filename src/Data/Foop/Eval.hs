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
import Data.Row.Dictionaries (Unconstrained1)

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
new_ :: forall surface roots query shoots context deps source state 
        .  Coherent source (Slot surface roots deps query)
        => TMVar (Entity source)
        -> Model (Slot surface roots deps query) 
        -> STM (Entity (Slot surface roots deps query))
new_ tmv mdl@(Model spec@(MkSpec iState qHandler renderR _) ms) = do 
  eState <- initE tmv spec ms  
  e <- newTVar $ mkEntity_ eState 
  pure $ Entity e 

-- | Constructs an entity from a model
new_' :: forall roots shoots query surface i state deps 
        . (Forall shoots SlotOrd, Coherent (Slot surface roots deps query) (Slot surface roots deps query))
       => Spec shoots state (Slot surface roots deps query)  
       -> Models roots 
       -> surface 
       -> IO (Entity (Slot surface roots deps query))
new_' spec@MkSpec{..}  ms surface  = case coherent @(Slot surface roots deps query) @(Slot surface roots deps query) of 
  (Dict,Dict,Dict,RootsW,RootsW,DepsW) -> do

          let Handler hq = handleQuery 

          let myChart :: Chart deps roots shoots 
              myChart = pos hq

          let roots = mkRoots myChart 

          let shoots = mkShoots myChart 

          env :: TMVar (Entity (Slot surface roots deps query)) <- newEmptyTMVarIO

          rs' <-  pure $ assemble1 env ms 

          rs''  <- assemble2 rs' 

          Handler h     <- pure handleQuery 

          deps  <- pure $ compat @(Slot surface roots deps query) @deps env 

          let here = Here :: Segment 'Begin ('Begin :> 'Start (Slot surface roots deps query))

          let evalSt = EvalState {_entity      = spec 
                                ,_state       = initialState 
                                ,_shoots      = mkStorage shoots 
                                ,_surface     = surface 
                                ,_roots       = ETree rs''
                                ,_environment = deps}
          eStore <- newTVarIO $ mkEntity_ @() evalSt
          atomically $ putTMVar env (Entity eStore)

          pure $  Entity eStore
 where 
  assemble2 :: Rec (R.Map STMNode roots) -> IO (Rec (R.Map ENode roots))
  assemble2 rx = R.traverseMap @Unconstrained1 @IO @STMNode @ENode @roots go rx 
   where 
     go :: forall x. STMNode x -> IO (ENode x)
     go (STMNode mx) = atomically mx 

  assemble1 :: All (Coherent (Slot surface roots deps query)) roots 
            => TMVar (Entity (Slot surface roots deps query))
            -> Models  roots 
            -> Rec (R.Map STMNode roots)
  assemble1 tmv (MkModels ms) = R.transform
                                  @(Coherent (Slot surface roots deps query))
                                  @roots 
                                  @(Model )
                                  @STMNode 
                                  go ms 
   where 
    go :: forall slot
        . (Coherent (Slot surface roots deps query) slot)
       => Model slot 
       -> STMNode slot 
    go mdl@(Model spec@MkSpec{..} ms) = case slotD :: DepsW (Compat (Slot surface roots deps query)) slot of 
      DepsW -> STMNode $ do 
        e <- new_ tmv mdl 
        pure . ENode $ e 
      
peekSurface :: Entity (Slot su rs ds q) -> STM su 
peekSurface (Entity e) = readTVar e >>= \t -> case pos t of 
  ExEvalState (EvalState _ _ _ _ surface _) -> pure surface  

mkRoots_ :: forall source roots su ds q 
          . (Forall roots Unconstrained1)  
         => RootsW (All (Coherent source)) (Slot su roots ds q)
         -> TMVar (Entity source)
         -> Models  roots  
         -> STM (ETree roots)
mkRoots_ rw@RootsW tmv models = ETree <$> go models   
  where 
    go :: Models roots -> STM (Rec (R.Map ENode roots))
    go  (MkModels ms) =  f $ R.transform
                                  @(Coherent source)
                                  @roots 
                                  @(Model )
                                  @STMNode 
                                  go2 ms 

    go2 :: forall slot
        . (Coherent source slot)
       => Model slot 
       -> STMNode slot 
    go2 mdl@(Model spec@MkSpec{..} ms) = case slotD :: DepsW (Compat source) slot of 
      DepsW -> STMNode $ do 
        e <- new_ tmv mdl 
        pure . ENode $ e 

    f :: Rec (R.Map STMNode roots) -> STM (Rec (R.Map ENode roots))
    f rx = R.traverseMap @Unconstrained1 @STM @STMNode @ENode @roots go rx 
     where 
      go :: forall x. STMNode x -> STM (ENode x)
      go (STMNode mx) = mx 

-- | Initializes an EvalState given a Spec 
initE :: forall source surface st q deps roots shoots i
       . Coherent source (Slot surface roots deps q) 
      => TMVar (Entity source)
      -> Spec shoots st (Slot surface roots deps q)
      -> Models roots 
      -> STM (EvalState deps roots shoots surface st q) 
initE  tmv espec@MkSpec{..} roots = case coherent @source @(Slot surface roots deps q) of 
  (d1@Dict,d2@Dict,d3@Dict,rw1@RootsW,rw2@RootsW,DepsW) -> do 
        rs            <-  mkRoots_ rw1 tmv roots 
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
    go ex@(ExEvalState est@(EvalState entity@(MkSpec iState (Handler hQuery) rendr _) sta str su loc env)) 
      = Transformer $ \qx -> 
          case apNT (extract hQuery) (Q . liftCoyoneda $ qx)  of 
            EntityM m -> do  
              let st = foldF (evalF  (EvalState entity sta str su loc env)) m
              ST.runStateT st ex

-- don't export this
-- | Runs an entity. For internal use only; you should use `tell` and `request` instead of this. 
run :: forall i su cs ds q x. q x -> Entity (Slot su cs ds q) -> IO x
run i (Entity tv) =  do
    e <- readTVarIO tv  -- reads the store from the tvar 
    Transformer f <- pure $ extract e 
    (x,st) <- f i -- apply the i-o transformer to some input 
    let newObj = withExEval st $ \x ->  mkEntity_ @i x  -- recreate the store comonad thingy from the new state 
    atomically $ writeTVar tv newObj -- write new store thingy to tvar 
    pure x

-- internal, don't export
-- | Retrieves the map of the entity's children. For internal use.
getShoot :: forall  label shoots slot roots st q deps i
         . (KnownSymbol label, HasType label (IxSlot i slot) shoots) 
        => EntityM deps roots shoots st q IO (ELeaf (IxSlot i slot))
getShoot = EntityM . liftF $ GetShoot (ShootKey :: ShootKey label shoots (IxSlot i slot)) id

-- don't export 
-- | `getSlot` but with a SlotKey (which serves as a dictionary for ChildC) instead of the ChildC constraint 
getShoot' ::  ShootKey label shoots slot
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
tell :: forall label shoots roots  i su cs ds q state query deps  
      . ( HasType label (IxSlot i (Slot su cs ds q)) shoots, KnownSymbol label)
     => i
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
tell i = tell_ @label i

tell_ :: forall label shoots roots  i su cs ds q state query deps  
      . ( HasType label (IxSlot i (Slot su cs ds q)) shoots , KnownSymbol label)
     => i
     -> Tell q
     -> EntityM deps roots shoots state query IO ()
tell_ i q = do
  ELeaf mySlot <- getShoot @label
  case M.lookup i mySlot of
    Nothing -> pure ()
    Just e  -> do
      lift (run (mkTell q) e)
      pure ()

-- | `tellAll q` executes a tell query for every child entity at a given slot. 
--   
--    Like `tell`, this requires a type application for the child label. 
-- 
--    E.g. `tell @"childLabel" MyQuery` 
tellAll :: forall label shoots roots  i su cs ds q state query deps  
      . (HasType label (IxSlot i (Slot su cs ds q)) shoots, KnownSymbol label)
     =>  Tell q
     -> EntityM deps roots shoots state query IO ()
tellAll q = do
  ELeaf mySlot <- getShoot @label @shoots 
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
request :: forall label i su cs ds q roots shoots state query x deps  
      . (HasType label (IxSlot i (Slot su cs ds q)) shoots, KnownSymbol label)
     => i
     -> Request q x
     -> EntityM deps roots shoots state query IO (Maybe x)
request i = request_ @label  i

request_ :: forall label i su cs ds q roots shoots state query x deps 
      . (HasType label (IxSlot i (Slot su cs ds q)) shoots, KnownSymbol label)
     => i
     -> Request q x
     -> EntityM deps roots shoots state query IO (Maybe x)
request_ i q = do
  ELeaf mySlot <- getShoot @label
  case M.lookup  i mySlot of
    Nothing -> pure Nothing
    Just e  -> do
      o <- lift (run (mkRequest q) e)
      pure (Just o)

-- | Like `tellAll` but for requests. Requires a type application for the child label.
requestAll :: forall label i su cs ds q roots shoots state query deps x 
      . (HasType label (IxSlot i (Slot su cs ds q)) shoots, KnownSymbol label)
     => Request q x
     -> EntityM deps roots shoots state query IO [x]
requestAll q = do
  ELeaf mySlot <- getShoot @label
  let slotKeys = M.keys mySlot
  catMaybes <$> mapM (\ i -> request_ @label  i q) slotKeys

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
    MkSpec iState (Handler hQuery) renderR _  -> 
      case apNT (extract hQuery) (Q q) of
        EntityM ef -> foldF (evalF (EvalState {..})) ef

  GetShoot key@ShootKey f ->  pure . f $ lookupLeaf key _shoots

  GetRoot skey@SlotKey f -> do
    (ETree roots) <- pure _roots 
    pure . f $ getRootWithKey skey roots  


  -- GHC doesn't get as mad if we do line-by-line "imperative style" vs trying to compose everything together
  Create slot l i e' a -> case slot of
    ShootKey -> undefined {-- 
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
   getRootWithKey :: forall l roots slot. SlotKey l roots slot -> Rec (R.Map ENode roots) -> ENode slot
   getRootWithKey SlotKey nodes = case deriveHas' @ENode @l @roots @slot of 
     Dict -> nodes R..! (Label @l)

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
delete :: forall label roots shoots state i su cs ds q query deps
      . (HasType label (IxSlot i (Slot su cs ds q)) shoots
      ,  KnownSymbol label) 
     => i 
     -> EntityM deps roots shoots state query IO ()
delete i = EntityM . liftF $ Delete (ShootKey :: ShootKey label shoots (IxSlot i (Slot su cs ds q))) i ()

-- | Creates a child component at the designaed label and index from the Prototype argument.
-- 
--   Requires a type application for the label.

create :: forall l i cs  su q deps slot state query roots shoots  ds loc
        . (Ord i
        , Forall shoots SlotOrd
        , KnownSymbol l
        , HasType l (IxSlot i (Slot su cs ds q)) shoots) 
       => i
       -> Model (Slot su cs ds q)
       -> EntityM deps roots shoots state query IO ()
create  i p = EntityM . liftF $ Create (ShootKey @l ) Label i p ()



observe :: forall l i su cs ds q deps roots shoots state query m a 
          . (Functor m
          , KnownSymbol l
          , HasType l (Slot su cs ds q) deps) 
         => Label l 
         -> (su -> a) 
         -> EntityM deps roots shoots state query m a
observe l f = EntityM . liftF $ Interact l (\(ENode e) -> f <$> peekSurface e)
