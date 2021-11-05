{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Foop.Slot where


import Data.Foop.Types
import Data.Row
import qualified Data.Row.Records as R
import qualified Data.Map as M
import Data.Proxy
import Data.Default
import Control.Concurrent.STM
import Data.Kind
import Control.Lens.Getter
import Control.Lens.Fold
import Data.Constraint
import Data.Foop.Dictionary
import Control.Comonad.Store
import Data.Coerce


-- | Given an Entity, renders its surface. Doesn't run the IO action.
observeE :: forall slot
         .  Entity slot
         -> STM (RenderLeaf slot)
observeE (Entity tv) =  do
  e <- readTVar tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> do
      let surface = render (renderer  _entity)  _state
      children <- toSurface (slots _entity) _storage
      pure $ MkRenderLeaf surface (MkRenderTree children)


lookupStorage :: forall label slots slot
               . SlotKey label slots slot
              -> Rec (R.Map StorageBox slots)
              -> StorageBox slot
lookupStorage key@SlotKey storage = withDict (deriveStoreHas key) $ storage .! (Label @label)


{--
lookupNode :: forall label slots slot
               . SlotKey label slots slot
              -> RenderTree slots
              -> RenderBranch slot
lookupNode key@SlotKey (MkRenderTree renderTree)
  = withDict (deriveSurfaceHas key)
  $ renderTree .! (Label @label)

modifyNode :: forall label slots slot
               . SlotKey label slots slot
              -> (RenderBranch slot -> RenderBranch slot)
              -> RenderTree slots
              -> RenderTree slots
modifyNode key@SlotKey f tree@(MkRenderTree  renderTree)
  =  withDict (deriveSurfaceHas key)
  $ case lookupNode key tree of
      oldNode -> let newNode = f oldNode
                     newTree = R.update (Label @label) newNode renderTree
                 in MkRenderTree  newTree

insertSurface :: forall i su cs q
               . Ord i
              => i
              -> RenderLeaf '(i,su,RenderTree cs,q)
              -> RenderBranch '(i,su,RenderTree cs,q)
              -> RenderBranch '(i,su,RenderTree cs,q)
insertSurface i leaf@(MkRenderLeaf s r) (MkRenderBranch  m)
  = MkRenderBranch $ M.insert (Indexed Index i) leaf m

deleteSurface :: forall i su cs q
               . Ord i
              => i
              -> RenderBranch '(i,su,RenderTree cs,q)
              -> RenderBranch '(i,su,RenderTree cs,q)
deleteSurface i (MkRenderBranch  m)
  = MkRenderBranch $ M.delete (Indexed Index i) m
--}

modifyStorage :: forall label slots slot
               . SlotKey label slots slot
              -> (StorageBox slot -> StorageBox slot)
              -> Rec (R.Map StorageBox slots)
              -> Rec (R.Map StorageBox slots)
modifyStorage key@SlotKey f storage
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

newtype IONode (slot :: SlotData) = IONode {ioNode :: STM (RenderBranch slot)}

toSurface :: forall slots. (Forall slots SlotOrdC)
          => Proxy slots
          -> Rec (R.Map StorageBox slots)
          -> STM (Rec (R.Map RenderBranch slots))
toSurface proxy = R.traverseMap @SlotOrdC @STM @StorageBox @RenderBranch @slots go
  where
    go :: forall slot
        . SlotOrdC slot
       => StorageBox slot
       -> STM(RenderBranch slot)
    go box = ioNode $ toRenderBranch box

toRenderBranch :: StorageBox slot
               -> IONode slot 
toRenderBranch (MkStorageBox  m) = IONode $ do
  rm <- traverse observeE m
  pure $ MkRenderBranch rm

bop = mkStorage (Proxy @TestRow)

mkRenderTree :: ( AllUniqueLabels slots
                , AllUniqueLabels (R.Map Proxy slots)
                , Forall slots SlotOrdC
                , Forall (R.Map Proxy slots) Default
                , R.Map RenderBranch slots1 ~ R.Map RenderBranch slots2
                ) => Proxy slots 
                  -> IO (RenderTree slots)
mkRenderTree proxy = MkRenderTree <$> atomically (toSurface proxy (mkStorage proxy))

bebop :: RenderTree TestRow 
bebop = undefined -- MkRenderTree $ unsafePerformIO . atomically $ toSurface (Proxy @TestRow) bop

mkStorage :: (AllUniqueLabels slots, AllUniqueLabels (R.Map Proxy slots),
 Forall slots SlotOrdC, Forall (R.Map Proxy slots) Default) =>
 Proxy slots -> Rec (R.Map StorageBox slots)
mkStorage proxy = toStorage proxy $ mkProxy  proxy

nodes :: forall slots. RenderTree slots -> Rec (R.Map RenderBranch slots)
nodes = coerce

type NodeC label slots slot = (HasType label slot slots, SlotOrdC slot, ChildC label slots slot, SlotConstraint slots)

branch :: forall label slots slot
      . NodeC label slots slot 
     => Getter (RenderTree slots) (RenderBranch slot)
branch = to (branch_ @label @slots @slot)

branch_ :: forall label slots slot
      . NodeC label slots slot 
      => RenderTree slots
      -> RenderBranch slot
branch_ (MkRenderTree t) = withDict (deriveSurfaceHas (SlotKey @label @slots @slot)) $ t .! (Label @label)

type MaybeLeaf :: SlotData -> Type 
newtype MaybeLeaf slot = MaybeLeaf {maybeLeaf :: Maybe (RenderLeaf slot)}

leaf :: forall i su cs q 
      . (SlotOrdC (Slot i su cs q))
     => i 
     -> Fold (RenderBranch (Slot i su cs q)) (RenderLeaf (Slot i su cs q))
leaf i = folding $ leaf_ @i @su @cs @q i 

leaf_ :: forall i su cs q 
      . (SlotOrdC (Slot i su cs q))
     => i
     -> RenderBranch (Slot i su cs q)
     -> Maybe (RenderLeaf (Slot i su cs q))
leaf_ i (MkRenderBranch m) = M.lookup (Indexed Index i) m

surface :: forall i su cs q 
         . SlotOrdC (Slot i su cs q)
        => Getter (RenderLeaf (Slot i su cs q)) su 
surface = to surface_ 

surface_ :: forall i su cs q 
         . SlotOrdC (Slot i su cs q)
        => RenderLeaf (Slot i su cs q)
        -> su 
surface_ (MkRenderLeaf s t) = s 

deep :: forall i su cs q
      . SlotOrdC (Slot i su cs q)
     => Getter (RenderLeaf (Slot i su cs q)) (RenderTree cs)
deep = to deep_

deep_ :: forall i su cs q 
       . SlotOrdC (Slot i su cs q)
      => RenderLeaf (Slot i su cs q)
      -> RenderTree cs 
deep_ (MkRenderLeaf s t) = t 

test = nodes bebop 

test1 = bebop ^? (branch @"slot1" . leaf 2 . surface)