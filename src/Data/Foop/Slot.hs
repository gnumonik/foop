{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE QuantifiedConstraints #-}

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
import Data.Row.Internal
import GHC.TypeLits (Symbol, TypeError)
import GHC.Base (Any)
import Control.Lens (Optic', Profunctor, Lens')
import Data.Singletons.Prelude.Eq
import Data.Singletons (KindOf)
import qualified Data.Constraint.Forall as DC

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

lookupSurface :: forall label slots slot 
              . SlotKey label slots slot 
             -> RenderTree slots 
             -> RenderBranch slot 
lookupSurface key@SlotKey (MkRenderTree cs) = withDict (deriveSurfaceHas key) $ cs .! (Label @label) 

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
       -> STM (RenderBranch slot)
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

type NodeC label slot slots = (HasType label slot slots, SlotOrdC slot, ChildC label slots slot, SlotConstraint slots)

open :: forall c r. BoxedContext c -> (forall context. c context => RenderLeaf context -> r) -> r 
open (BoxedContext cxt) f = f cxt 

branch :: forall label slot slots 
      . NodeC label slot slots 
     => Getter (RenderTree slots) (RenderBranch slot)
branch = to (branch_ @label @slots @slot)


branch_ :: forall label slots slot
      . NodeC label slot slots  
      => RenderTree slots
      -> RenderBranch slot
branch_ (MkRenderTree t) = withDict (deriveSurfaceHas (SlotKey @label @slots @slot)) $ t .! (Label @label)

type MaybeLeaf :: SlotData -> Type 
newtype MaybeLeaf slot = MaybeLeaf {maybeLeaf :: Maybe (RenderLeaf slot)}

leaf :: forall i su cs q 
      . Ord i
     => i 
     -> Fold (RenderBranch (Slot i su cs q)) (RenderLeaf (Slot i su cs q))
leaf i = folding $ leaf_ @i @su @cs @q i 

leaf_ :: forall i su cs q 
      .  Ord i 
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
      .  Getter (RenderLeaf (Slot i su cs q)) (RenderTree cs)
deep = to deep_

deep_ :: forall i su cs q 
       . RenderLeaf (Slot i su cs q)
      -> RenderTree cs 
deep_ (MkRenderLeaf s t) = t 

test = nodes bebop 

test1 x = x ^? (branch @"slot1" . leaf 2 . surface)

deNormalize :: NormalizedPath root path -> Path root path 
deNormalize = \case 
  Start' -> Start 
  Branch' SlotKey np -> Branch  (deNormalize np) 
  Leaf' i np -> Leaf i (deNormalize np)
  Down' np -> Down (deNormalize np)


(||>) :: Path root old -> (Path root old -> Path root new) -> Path root new 
a ||> f = f a 
infixl 1 ||>

ebranch :: forall i su cs q a l b 
         . NormalizedPath (Slot i su cs q) (a :> 'Branch_ (l ':= b))
        -> Entity (Slot i su cs q)
        -> STM (Maybe (Rec (l .== StorageBox b)))
ebranch = undefined 

type PathErr root path = Path root path

doop2 =   Start 
      ||> Down 
      ||> Branch @"rootSlotA" 

type family Target (p :: PathDir) :: T (Row SlotData) Symbol SlotData where 
  Target (a :> b)   = b 

class Certainly (slot :: SlotData) (p :: PathDir) where 
  mkGetter :: NormalizedPath slot p -> Getter (RenderLeaf slot) (TraceS p)

instance Certainly (Slot i su cs q) ('Begin :> 'Leaf_ (Slot i su cs q)) where 
  mkGetter Start' = to id

instance Certainly root (old :> 'Down_ slots) => Certainly root ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q)) where 
  mkGetter (Branch' key old) = mkGetter old . to (lookupSurface key)

instance  Certainly (Slot i su cs q) ('Begin :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
  mkGetter (Down' Start') = to $ \(MkRenderLeaf su cs) -> cs

class Possibly (slot :: SlotData) (p :: PathDir) where 
  mkFold :: NormalizedPath slot p -> Fold (RenderLeaf slot) (TraceS p)
{--
instance Possibly (Slot i su cs q) ('Begin :> 'Leaf_ (Slot i su cs q)) where 
  mkFold Start' = to id
--}
instance Possibly root (old :> 'Down_ slots) => Possibly root ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q)) where 
  mkFold (Branch' key old) = mkFold old . to (lookupSurface key)

instance  Possibly (Slot i su cs q) ('Begin :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
  mkFold (Down' Start') = to $ \(MkRenderLeaf su cs) -> cs

instance Possibly root (old :> 'Branch_ (l ':= Slot i su cs q)) => Possibly root (old :> 'Branch_ (l ':= Slot i su cs q) :> 'Leaf_ (Slot i su cs q)) where 
  mkFold (Leaf' i old) = mkFold old . leaf i

instance Possibly root (old1 :> 'Leaf_ (Slot i su cs q)) => Possibly root (old1 :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
  mkFold (Down' old) = mkFold old . to (\(MkRenderLeaf su cs) -> cs)

fetch :: Certainly root path => NormalizedPath root path -> RenderLeaf root -> TraceS path 
fetch npath leaf = leaf ^. mkGetter npath 

search :: Possibly root path => NormalizedPath root path -> RenderLeaf root -> Maybe (TraceS path)
search npath leaf = leaf ^? mkFold npath 

applyPath :: forall slot t t'. t ~ t' => Path slot t' -> Path slot t 
applyPath path = path 

applyPathN :: forall slot t. NormalizedPath slot t -> NormalizedPath slot t 
applyPathN path = path 

applyAtlas :: forall slot paths. Atlas slot paths -> Atlas slot paths 
applyAtlas = id 


hmbm = applyAtlas @MySlot debop 

debop =  AddPath (Start ||> Down) Empty 

doop3 = Start ||> Down ||> Branch @"rootSlotA" ||> Leaf True ||> Up

doop4 = Start ||> Up

testRLeaf :: RenderLeaf MySlot 
testRLeaf = undefined 


bebop3 =  normalize (applyPath @MySlot doop3)

-- pth = search yoyo testRLeaf 

bodoop :: forall t slot. t ~ Maybe (RenderLeaf slot) => Maybe (RenderLeaf slot) -> Proxy (Maybe (RenderLeaf slot))
bodoop _ = Proxy 


yoyo  = mergePaths   (applyPath @MySlot (  Start 
                                         ||> Down 
                                         ||> Branch @"rootSlotB" 
                                         ||> Leaf 'a' ))  (Start ||> Down)


type MySlot = Slot Bool Bool Row1 Maybe 

type Row1 :: Row SlotData 
type Row1 = "rootSlotA" .== Slot Bool Int Empty (Either String)
         .+ "rootSlotB" .== Slot Char Int Row2 Maybe 

type Row2 :: Row SlotData 
type Row2 = "depth1SlotA" .== Slot Rational Double Empty Maybe 
         .+ "depth1SlotB" .== Slot Int String Row3 (Either Bool)

type Row3 :: Row SlotData 
type Row3 = "depth2SlotA" .== Slot String () Empty []

type HasSurfaceF :: Type -> SlotData -> Constraint 
type family HasSurfaceF su slot where 
  HasSurfaceF su (Slot i su cs q) = () 

type HasChildF :: Symbol -> SlotData -> SlotData -> Constraint 
type family HasChildF l slot parent where 
  HasChildF l (Slot i su cs r) (Slot pi psu pcs pr) = HasType l (Slot i su cs r) pcs

type DeepCF :: (Row SlotData -> Constraint) -> SlotData -> Constraint 
type family DeepCF c slot where 
  DeepCF c (Slot i su cs r) = c cs 

class HasSurfaceF su slot => HasSurface su slot where 
  hasSurface :: Dict (HasSurfaceF su slot) 
  hasSurface = Dict 

instance HasSurfaceF su slot => HasSurface su slot

class HasChildF l childSlot parentSlot => HasChild l childSlot parentSlot where 
  hasChild :: Dict (HasChildF l childSlot parentSlot)
  hasChild = Dict 

instance HasChildF l childSlot parentSlot => HasChild l childSlot parentSlot 

class DeepCF c slot => DeepC c slot where 
  deepC :: Dict (DeepCF c slot)
  deepC = Dict 

instance DeepCF c slot => DeepC c slot 


