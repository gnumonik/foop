module Data.Foop.Prototype where


import Data.Foop.Types
import Data.Proxy
import Data.Row
import Data.Kind
import Data.Functor.Coyoneda ( Coyoneda(..), liftCoyoneda )
import qualified Data.Row.Records as R
import Data.Default
import qualified Data.Map as M
import Data.Constraint

-- | Apply a natural transformation to (probably) a functor 
apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

-- | Empty slot record. For convenience.
emptySlots :: Proxy Empty 
emptySlots = Proxy 

-- | Makes a renderer that always returns (IO ()) as the side effect of rendering 
mkSimpleRender :: (RenderTree slots -> state -> surface) 
               -> Renderer slots state surface 
mkSimpleRender f = MkRenderer f (const $ pure ()) 

-- | `queryHandler` takes a function of type (forall x. query x -> EntityM slots state query m)
--   and packages it into a boxed natural transformation. 
queryHandler :: forall slots state query m 
        . Functor m
       => (query ~> EntityM slots state query m)
       -> (AlgebraQ query :~> EntityM slots state query m)
queryHandler eval = NT go 
  where 
    go :: forall x. AlgebraQ query x -> EntityM slots state query m x
    go (Q q) = unCoyoneda (\g -> fmap  g . eval) q

    unCoyoneda :: forall (q :: Type -> Type) 
                         (a :: Type) 
                         (r :: Type)
                . (forall (b :: Type). (b -> a) -> q b -> r)
               -> Coyoneda q a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

-- | Constructs a Prototype provides the Row of Slotdata for the prototype satisfies SlotConstraint
prototype :: -- SlotConstraint slots => 
             Spec slots surface state query 
          -> Prototype surface slots query 
prototype = Prototype 

{--
-- don't export
mapSlots :: (Rec (MkRenderTree slots) -> Rec (MkRenderTree slots)) -> RenderNode r slots -> RenderNode r slots 
mapSlots f (RenderNode r slots) = RenderNode r (f slots)

instance (Forall (MkRenderTree slots) Show, Show r) => Show (RenderNode r slots) where 
  show (RenderNode r tree) = "RenderNode " <> show r <> " " <> show tree 
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


class ProxyC c t => ProxyC' c t 
instance ProxyC c t => ProxyC' c t 

type family SlotC (slot :: SlotData) :: Constraint where 
  SlotC '(i,s,RenderTree cs,q) = Ord i 

class SlotC slot => SlotOrdC slot 
instance SlotC slot => SlotOrdC slot 

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