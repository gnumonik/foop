{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
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
import Control.Comonad.Store 


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

-- | `queryHandler` takes a function of type (forall x. query x -> EntityM slots state query m)
--   and packages it into a boxed natural transformation. 
queryHandler :: forall query roots shoots state deps 
        . (query ~> EntityM deps roots shoots state query IO)
       -> AlgebraQ query :~> EntityM deps roots shoots state query IO 
queryHandler eval = NT $ \(Q q) -> unCoyoneda (\g -> fmap g . eval) q 

mkQHandler_ :: forall slot query roots shoots state 
             . (forall x. query x -> EntityM  Empty roots shoots state query IO x)
             -> Handler slot query Empty roots shoots state
mkQHandler_ f = mkQHandler NoDeps (const f)   

mkQHandler :: forall slot query deps roots shoots state  
            . MkPaths slot deps 
           -> (forall x. MkPaths slot deps -> query x -> EntityM  deps roots shoots state query IO x)
           -> Handler slot query deps roots shoots state 
mkQHandler paths eval = Handler $ store (accessor eval) paths 
  where 
    accessor :: (forall x. MkPaths slot deps -> query x -> EntityM deps roots shoots state query IO x)
             -> MkPaths slot deps
             -> AlgebraQ query :~> EntityM deps roots shoots state query IO
    accessor f' paths = NT $ \(Q q) -> unCoyoneda (\g -> fmap g . eval paths) q 

unCoyoneda :: forall (q :: Type -> Type) 
                     (a :: Type) 
                     (r :: Type)
            . (forall (b :: Type). (b -> a) -> q b -> r)
            -> Coyoneda q a 
            -> r 
unCoyoneda f (Coyoneda ba fb) = f ba fb  

