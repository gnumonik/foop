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
import Data.Void (Void)
import Control.Monad.Identity

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

{--
deNormalize :: NormalizedPath path -> Path path 
deNormalize = \case 
  Start' -> Start 
  Branch' SlotKey np -> Branch  (deNormalize np) 
  Leaf' i np -> Leaf i (deNormalize np)
  Down' np -> Down (deNormalize np)
--}




ebranch :: forall i su cs q a l b 
         . NormalizedPath  (a :> 'Branch_ (l ':= b))
        -> Entity (Slot i su cs q)
        -> STM (Maybe (Rec (l .== StorageBox b)))
ebranch = undefined 






applyPath :: forall slot f p. RootOf p ~ slot => f p -> f  p 
applyPath path = path 

applyPathN :: forall slot p. RootOf p ~ slot => NormalizedPath p -> NormalizedPath p 
applyPathN path = path 

{--
findPath :: forall start end. Path start end -> Entity start -> STM (Maybe (Entity end))
findPath (MkPath path) (Entity e) = readTVar e >>= go path 
  where 
  --  go ::  PathFinder' path -> EntityStore root loc su cs q -> STM (Maybe (Entity end))
--}



testRLeaf :: RenderLeaf MySlot 
testRLeaf = undefined 



reifyPF :: forall start root path. root ~ RootOf path => PathFinder start path -> PathFinder start path 
reifyPF = id 

testPF = fixPath $ reifyPF @'Begin @MySlot $ Here +> Child @"rootSlotA" True +> Parent 


-- testApPF = fixPath $ applyPath @MySlot testPF 


-- pth = search yoyo testRLeaf 

bodoop :: forall t slot. t ~ Maybe (RenderLeaf slot) => Maybe (RenderLeaf slot) -> Proxy (Maybe (RenderLeaf slot))
bodoop _ = Proxy 




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

type Joined :: PathDir -> PathDir -> Type 
data Joined parent child where 
  MkJoined :: PathFinder' (FixPath (JoinPath parent child)) 
           -> Joined parent  child

type EndOfF :: Type -> SlotData 
type family EndOfF path where 
  EndOfF (PathFinder 'Begin path) = EndOf path 


type Directed :: PathDir ->  PathDir -> Type 
data Directed parent child where 
  MkDirected :: Path (RootOf (FixPath (JoinPath parent child))) (EndOf (FixPath (JoinPath parent child)))
             -> Directed parent child 


-- this is really neat 
allHave :: forall f c children 
        . AllHave f c children
       => Rec children 
       -> Rec (R.Map (HasA c f) children)
allHave = R.map @(Has c f) go 
  where 
    go :: forall t 
        . Has c f t 
       => t 
       -> HasA c f t 
    go t = case hasW :: HasW c f t of 
      h@HasW -> HasA t 

-- finish tomorrow
locate :: forall i su cs q  target 
        . Path (Slot i su cs q) target 
       -> Entity (Slot i su cs q) 
       -> STM (Maybe (Entity target))
locate (MkPath pf') e = go e pf'
  where 
   go :: forall path
       . (RootOf path ~ Slot i su cs q, EndOf path ~ target)  
      => Entity (Slot i su cs q) 
      -> PathFinder' path 
      -> STM (Maybe (Entity target))
   go (Entity e) Here' = pure . Just $ Entity e 
   go (Entity e) child@(Child' i rest) = case normalizePF child of 
     (Leaf' i (Branch' s@SlotKey (Down' rest'))) -> 
       withDict (deriveStoreHas s) $ do 
         ExEvalState (EvalState _ _ storage _ _ _) <- pos <$> readTVar e 
         let box = lookupStorage s storage 
         error "boom"
         -- CANT DO IT ALL IN ONE FUNCTION, too many nested existentials


-- HasA c f t ==> forall a. t ~ f a, c a 
-- HasA2 ==> forall a. t ~ f a, t' ~ g a, c a 

data MapExists :: (k -> Constraint) ->  (k -> Type) -> (k -> Type) -> Type -> Type where 
  MapExists :: forall k 
                 (f :: k -> Type)
                 (g :: k -> Type)
                 (c :: k -> Constraint)
                 t 
         . (forall (x :: k). c x => f x -> g x)
           -> HasA c f t 
           -> MapExists c f g t

extractEx :: forall c f g t t' a. (t ~ f a, t' ~ g a) => MapExists c f g t -> t'
extractEx mx@(MapExists f (HasA ft)) = case hasW :: HasW c f t of 
  HasW -> f ft 


rmapEx :: MapExists c f g t
         -> (forall (x :: k). c x => g x -> h x)
         -> MapExists c f h t
rmapEx mx@(MapExists f (HasA ft)) g = MapExists (g . f) (HasA ft)

exMap :: forall c f g t r
       . MapExists c f g t
      -> (forall a. c a => g a -> r)
      -> r 
exMap (MapExists f (HasA ft)) g = g (f ft)

allTransform :: forall c f g h children 
              . Forall children Unconstrained1 
             => Rec (R.Map (MapExists c f g) children)
             -> (forall x. c x => g x -> h x) 
             -> Rec (R.Map (MapExists c f h) children)
allTransform old f = R.transform' @children @(MapExists c f g) @(MapExists c f h) go old 
  where 
    go :: forall t. MapExists c f g t -> MapExists c f h t
    go mx = rmapEx mx f 

allTo :: forall f g c children 
       .  Forall children (Has c f) 
      => (forall a. c a => f a -> g a ) 
      -> Rec (R.Map (HasA c f ) children)
      -> Rec (R.Map (MapExists c f g) children)
allTo f = R.transform @(Has c f) @children @(HasA c f) @(MapExists c f g) go 
  where 
    go :: forall t. Has c f t => HasA c f t -> MapExists c f g t 
    go (HasA ft) = MapExists f (HasA ft)



unifyPaths :: forall parent children 
            . ( Forall children (Has (ExtendPath parent) (PathFinder 'Begin))
              , Forall children Unconstrained1)
           => PathFinder 'Begin parent 
           -> Rec children 
           -> Rec (R.Map (MapExists (ExtendPath parent) (PathFinder 'Begin) (Directed parent)) children)
unifyPaths pt rs = c 
  where 
    a :: Rec (Map (HasA (ExtendPath parent) (PathFinder 'Begin)) children)
    a = allHave 
          @(PathFinder 'Begin) 
          @(ExtendPath parent)  
          rs 

    b :: Rec (R.Map (MapExists (ExtendPath parent) (PathFinder 'Begin) (Joined parent)) children)
    b = allTo 
          @(PathFinder 'Begin) 
          @(Joined parent) 
          @(ExtendPath parent) 
          @children 
          f a 

    c :: Rec (R.Map (MapExists (ExtendPath parent) (PathFinder 'Begin) (Directed parent)) children)
    c = allTransform 
          @(ExtendPath parent) 
          @(PathFinder 'Begin) 
          @(Joined parent) 
          @(Directed parent) 
          @children 
          b g 

    f :: forall (x :: PathDir). ExtendPath parent x => PathFinder 'Begin x -> Joined parent x 
    f pf = MkJoined $ extendPath pt pf 

    g :: forall (x :: PathDir). ExtendPath parent x => Joined parent x -> Directed parent x
    g (MkJoined pf) = MkDirected (MkPath pf)

{-- 
unifyPaths2 :: forall parent children 
             . ( Forall children Unconstrained1
               , Forall (R.Map (Directed (RootOf parent)) children) Unconstrained1)
            => Rec (R.Map (Joined parent) children)
            -> Rec (R.Map (Directed (RootOf parent)) children)
unifyPaths2  = R.transform' @children @(Joined parent) @(Directed (RootOf parent)) go 
  where 
    go :: forall path
        .  Joined parent path
        -> Directed (RootOf parent) path
    go (MkJoined pf') = undefined -- MkDirected $ MkPath pf'


unifyPaths1 :: forall parent children 
            . AllExtend parent children 
           => PathFinder 'Begin parent 
           -> Rec children 
           -> Rec (R.Map (Joined parent) children)
unifyPaths1 parent  = R.map @(Has (ExtendPath parent) (PathFinder 'Begin)) go' 
  where 
    go' :: forall t. Has (ExtendPath parent) (PathFinder 'Begin) t => t -> Joined parent t
    go' = go parent 

    go :: forall t
        . Has (ExtendPath parent) (PathFinder 'Begin) t
       => PathFinder 'Begin parent  
       -> t
       -> Joined parent t
    go p c = case hasW :: HasW (ExtendPath parent) (PathFinder 'Begin) t of
      h@HasW -> MkJoined $ extendPath p c 

--}