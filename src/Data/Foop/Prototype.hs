{-# LANGUAGE ConstraintKinds #-}
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
mkSimpleRender :: (state -> surface) 
               -> Renderer state surface 
mkSimpleRender f = MkRenderer f (const $ pure ()) 

-- | `queryHandler` takes a function of type (forall x. query x -> EntityM slots state query m)
--   and packages it into a boxed natural transformation. 
queryHandler :: forall context slots state query m 
        . Functor m
       => (query ~> EntityM context slots state query m)
       -> (AlgebraQ query :~> EntityM context slots state query m)
queryHandler eval = NT go 
  where 
    go :: forall x. AlgebraQ query x -> EntityM context slots state query m x
    go (Q q) = unCoyoneda (\g -> fmap  g . eval) q

    unCoyoneda :: forall (q :: Type -> Type) 
                         (a :: Type) 
                         (r :: Type)
                . (forall (b :: Type). (b -> a) -> q b -> r)
               -> Coyoneda q a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

-- | Constructs a Prototype provides the Row of Slotdata for the prototype satisfies SlotConstraint
prototype :: forall slots surface query state context
           . (SlotConstraint slots, SlotOrdC context)
          => Spec slots surface state query context
          -> Prototype surface slots query context
prototype = Prototype 


{--
mkModel :: forall surface slots query (c :: SlotData -> Constraint ) state  
         . (SlotConstraint slots )
        =>  Proxy state -> (forall context. c context => Spec slots surface state query context)
        -> Model surface slots query c
mkModel proxy f = Model f 
--}
{--
-- don't export
mapSlots :: (Rec (MkRenderTree slots) -> Rec (MkRenderTree slots)) -> RenderNode r slots -> RenderNode r slots 
mapSlots f (RenderNode r slots) = RenderNode r (f slots)

instance (Forall (MkRenderTree slots) Show, Show r) => Show (RenderNode r slots) where 
  show (RenderNode r tree) = "RenderNode " <> show r <> " " <> show tree 
--}



