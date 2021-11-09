{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
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
import Control.Concurrent.STM
import qualified Data.Constraint.Forall as DC

explicitly :: forall k (c :: k -> Constraint) (a :: k) r 
            . (c a => r)
           -> (Dict (c a) -> r)
explicitly f = \d@Dict -> withDict d f 

mapE :: forall k (c :: k -> Constraint) (a :: k) r r'  
            . (c a => r)
           -> (r -> r')
           -> (Dict (c a) -> r')
mapE f g = \d@Dict -> withDict d g f 

mapC :: forall k (c :: k -> Constraint) (a :: k) r r' 
      . (c a => r)
     -> (r -> r')
     -> (c a => r')
mapC cr f = go 
 where 
   go :: c a => r'
   go = f cr 

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

instHandler :: forall context c slots state query. 
               (DC.Forall c, c context )
            => QHandler query c slots state 
            -> AlgebraQ query :~> EntityM c slots state query IO
instHandler (MkQHandler  handler) = case handler Dict of 
  handler' -> case DC.inst @c @context of 
    d -> case mapDict d (Dict @(DC.Forall c))  of 
      Dict ->  NT $ \(Q q) -> unCoyoneda (\g -> fmap g . handler Dict) q 


-- | `queryHandler` takes a function of type (forall x. query x -> EntityM slots state query m)
--   and packages it into a boxed natural transformation. 
queryHandler :: forall query c slots state   
        . (DC.Forall c => query ~> EntityM c slots state query IO)
       -> QHandler query c slots state  
queryHandler eval = MkQHandler $ explicitly eval 
  where 
    eval' :: Dict (DC.Forall c) -> (forall x. query x -> EntityM c slots state query IO x)
    eval' = explicitly eval 




    go :: (forall x. query x -> EntityM c slots state query IO x) -> (AlgebraQ query :~> EntityM c slots state query IO)
    go  f = NT $ \(Q q) -> unCoyoneda (\g -> fmap  g . f ) q

unCoyoneda :: forall (q :: Type -> Type) 
                      (a :: Type) 
                      (r :: Type)
            . (forall (b :: Type). (b -> a) -> q b -> r)
            -> Coyoneda q a 
            -> r 
unCoyoneda f (Coyoneda ba fb) = f ba fb  


unboxContext :: forall c r. TBoxedContext c 
             -> (forall cxt. Dict (c cxt) -> TVar (RenderLeaf cxt) -> r)
             -> r 
unboxContext (TBoxedContext cxt) f = f Dict cxt 


unboxContext' :: forall (c :: SlotData -> Constraint) r. TBoxedContext c 
             -> (forall i su cs q. Dict (c (Slot i su cs q)) -> TVar (RenderLeaf (Slot i su cs q)) -> r)
             -> r 
unboxContext' (TBoxedContext cxt) f = f Dict  cxt 


withModel :: forall surface slots query c r 
           . DC.Forall c 
          => Model surface slots query c 
          -> TBoxedContext c 
          -> (forall state cxt
              . c cxt 
             => TVar (RenderLeaf cxt)
             -> Spec slots surface state query c 
             -> r) 
          -> r 
withModel m box f = unboxContext box $ \d t -> go  d m t   f
  where 
    go :: forall cxt. 
          Dict (c cxt) 
       -> Model surface slots query c  
       -> TVar (RenderLeaf cxt) 
       -> (forall state cxt
              . c cxt 
             => TVar (RenderLeaf cxt)
             -> Spec slots surface state query c 
             -> r) 
       -> r
    go d@Dict (Model spec) tv g = g tv (spec Dict)


{--
-- | Constructs a Prototype provides the Row of Slotdata for the prototype satisfies SlotConstraint
prototype :: forall slots surface query state context
           . (SlotConstraint slots, SlotOrdC context)
          => Spec slots surface state query context
          -> Prototype surface slots query context
prototype = Prototype 
--}

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



