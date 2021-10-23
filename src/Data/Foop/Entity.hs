module Data.Foop.Entity  where

import Data.Kind ( Type, Constraint ) 
import Data.Foop.EntityF ( EntityM ) 
import Data.Functor.Coyoneda ( Coyoneda(..) )
import Data.Functor (($>))
import Data.Row.Records 
import GHC.TypeLits (Symbol)
import Data.Singletons hiding (type (~>))
import Data.Foop.DList 
import Data.Foop.EntityF (type SlotData)

type SlotOrdC :: (Type, Type -> Type, Type -> Type) -> Constraint 
class SlotOrdC slot where 
instance Ord i => SlotOrdC '(i,q,m) 

data Prototype :: Type ->  (Type -> Type) -> (Type -> Type) -> Type where 
  Prototype :: Spec slots r state query m 
         -> Prototype r query m

type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

newtype AlgebraQ query a =  Q (Coyoneda query a) 

type Spec :: Row SlotData -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type 
data Spec slots context state query m where 
  MkSpec :: Forall slots SlotOrdC => 
    { initialState   :: state -- For existential-ey reasons this has to be a function
    , queryHandler   :: AlgebraQ query :~> EntityM slots context state query m
    , render         :: state -> EntityM slots context state query m ()
    , slots          :: Proxy slots 
    } -> Spec slots context state query m 

defaultRender :: forall slots state  context query m 
               . state -> EntityM slots  context state query m ()
defaultRender = const . pure $ ()

queryAlgebra :: forall slots r s q m 
        . Functor m
       => ( q ~> EntityM slots r s q m)
       -> (AlgebraQ q :~> EntityM slots r s q m)
queryAlgebra eval = NT go 
  where 
    go :: forall x. AlgebraQ q x -> EntityM slots r s q m x
    go (Q q) = unCoyoneda (\g -> fmap  g . eval) q

    unCoyoneda :: forall (q :: Type -> Type) (a :: Type) (r :: Type)
                . (forall (b :: Type). (b -> a) -> q b -> r)
               -> Coyoneda q a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

prototype :: Spec slots r s q m 
         -> Prototype r q m 
prototype e = Prototype e 

