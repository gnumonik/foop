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

type SlotOrdC :: (Type, Type, Type -> Type, Type -> Type) -> Constraint 
class SlotOrdC slot where 
instance Ord i => SlotOrdC '(r,i,q,m) 

data Prototype :: Row SlotData -> Type -> Type ->  (Type -> Type) -> (Type -> Type) -> Type where 
  Prototype :: Forall slots SlotOrdC 
            => Spec slots rendered context state query m 
            -> Prototype slots rendered context query m

type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

newtype AlgebraQ query a =  Q (Coyoneda query a) 

{--

It seems like we have 2 options for 'render': 

  1) Parameterize the monad over some "render output" type and automatically construct a 
     "tree" (in practice it'd probably be a Row of...something). This is hard but doable. 

  2) Make the render function be of type `state -> IO ()`. This is easy and convenient but 
     it introduces IO in a weird place. 

So 1) seems preferable. In order to implement it, we'd have to add a type var parameter to 
the spec (but not the EntityF/M, I think) which would have to be visible in the spec and 
the EvalSpec. I'm not sure if we can existentialize it away in the ExEvalSpec but it's not a 
huge deal if we can't, just makes things a bit more complicated

The real problem is: How the fuck do we construct and manipulate the "tree"? And how do we restrict an 
entity's rendering capacity such that it can only affect the component of the render tree that it represents?
--}

type Spec :: Row SlotData -> Type -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type 
data Spec slots rendered context state query m where 
  MkSpec :: Forall slots SlotOrdC => 
    { initialState   :: state -- For existential-ey reasons this has to be a function
    , handleQuery    :: AlgebraQ query :~> EntityM slots context state query m
    , render         :: state -> rendered -- I don't like this being IO () but i can't see a way around it -_-
    , slots          :: Proxy slots 
    } -> Spec slots rendered context state query m 

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

prototype :: Forall slots SlotOrdC 
          => Spec slots rendered context state query m 
          -> Prototype slots rendered context query m 
prototype e = Prototype e 

