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
import Data.Row.Internal

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
queryHandler :: forall query roots state deps 
        . (query ~> EntityM deps roots state query IO)
       -> AlgebraQ query :~> EntityM deps roots state query IO 
queryHandler eval = NT $ \(Q q) -> unCoyoneda (\g -> fmap g . eval) q 

emptyChart :: Chart  Empty Empty 
emptyChart = MkChart {mkDeps = Proxy, mkRoots = Proxy}

mkQHandler_ :: forall  slot query  state 
             . (forall x. query x -> EntityM Empty Empty state query IO x)
             -> Handler slot query Empty Empty state
mkQHandler_ f = mkQHandler emptyChart (const f)   

mkQHandler :: forall source slot query deps roots  state  
            . Chart deps roots  
           -> (forall x. Chart  deps roots  -> query x -> EntityM  deps roots state query IO x)
           -> Handler  slot query deps roots state 
mkQHandler p eval = Handler $ store accessor p 
  where 
    accessor :: Chart deps roots -> AlgebraQ query :~> EntityM deps roots state query IO
    accessor p = NT $ \(Q q) -> unCoyoneda (\g -> fmap g . eval p) q 

unCoyoneda :: forall (q :: Type -> Type) 
                     (a :: Type) 
                     (r :: Type)
            . (forall (b :: Type). (b -> a) -> q b -> r)
            -> Coyoneda q a 
            -> r 
unCoyoneda f (Coyoneda ba fb) = f ba fb  

install :: Models rs -> Spec state (Slot su rs ds q) -> Model (Slot su rs ds q)
install ms spec = Model spec ms 
