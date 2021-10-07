module Data.Foop.Entity  where

import Data.Kind ( Type ) 
import Data.Foop.EntityF ( EntityM ) 
import Data.Functor.Coyoneda ( Coyoneda(..) )
import Data.Functor (($>))

data Prototype :: Type -> (Type -> Type) -> (Type -> Type) -> Type where 
  Prototype :: Spec r state query m 
         -> Prototype r query m

type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

newtype AlgebraQ query a =  Q (Coyoneda query a) 

type Spec :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type 
data Spec r state query m where 
  MkSpec ::
    { _init :: state -- For existential-ey reasons this has to be a function
    , _eval :: AlgebraQ query :~> EntityM r state query m  
    } -> Spec r state query m 

mkEval :: forall r s q m 
        . Functor m
       => ( q ~> EntityM r s q m)
       -> (AlgebraQ q :~> EntityM r s q m)
mkEval eval = NT go 
  where 

    go :: forall x. AlgebraQ q x -> EntityM r s q m x
    go (Q q) = unCoyoneda (\g -> fmap  g . eval) q

    unCoyoneda :: forall (q :: Type -> Type) (a :: Type) (r :: Type)
                . (forall (b :: Type). (b -> a) -> q b -> r)
               -> Coyoneda q a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

mkEntity :: Spec r s q m 
         -> Prototype r q m 
mkEntity e = Prototype e 


