module Data.Foop.Prototype where


import Data.Foop.Types
import Data.Proxy
import Data.Row
import Data.Kind
import Data.Functor.Coyoneda ( Coyoneda(..), liftCoyoneda )
import qualified Data.Row.Records as R
import Data.Default

-- | Apply a natural transformation to (probably) a functor 
apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

-- | Empty slot record. For convenience.
emptySlots :: Proxy Empty 
emptySlots = Proxy 

-- | Makes a renderer that always returns (IO ()) as the side effect of rendering 
mkSimpleRender :: (state -> surface) -> Renderer state surface 
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
prototype :: SlotConstraint slots
          => Spec slots surface state query 
          -> Prototype surface query 
prototype = Prototype 

-- don't export
mapSlots :: (Rec (MkRenderTree slots) -> Rec (MkRenderTree slots)) -> RenderNode r slots -> RenderNode r slots 
mapSlots f (RenderNode r slots) = RenderNode r (f slots)

instance (Forall (MkRenderTree slots) Show, Show r) => Show (RenderNode r slots) where 
  show (RenderNode r tree) = "RenderNode " <> show r <> " " <> show tree 

-- | Constructs an empty slot storage record.
mkStorage :: forall slots
           . StorageConstraint slots 
          => Proxy slots  -> Rec (MkStorage slots)
mkStorage proxy = R.default' @Default def

-- | Constructs an empty render tree.
mkRenderTree :: forall slots 
              . SlotConstraint slots 
             => Proxy slots -> Rec (MkRenderTree slots)
mkRenderTree proxy = R.default' @Default def 