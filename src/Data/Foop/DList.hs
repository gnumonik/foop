{-# LANGUAGE ConstraintKinds, IncoherentInstances #-}
module Data.Foop.DList where

import Data.Kind (Type, Constraint)
import Data.Singletons (Sing, withSingI, SomeSing (SomeSing), SingI (sing))
import qualified Data.List.NonEmpty as NE 
import Data.List.NonEmpty (NonEmpty(..))
import Data.Row
import Data.Row.Internal
import Data.Singletons.TypeLits (Symbol, withKnownSymbol)
import qualified Data.Row.Records as R
import Data.Constraint

{--

"Dependently typed" utilities. 

(:::) is kind of like Sigma from Data.Singletons.Sigma, except: 
  The kind is `forall k. (k -> Type) -> k -> Type` instead of `forall k -> (k ~> Type) -> Type` 
      - (~>) isn't injective, and we *need* injectivity for basically *everything* to work 
      - because (k -> Type) is a GADT-like type constructor with one "open" argument position, 
        we don't need visible dependent quantification
      - we don't actually need to map dependently across the pair here and that (i think?) 
        is the only thing that Sigma can do that our "dependent pair" can't 

DList is an abstraction for a list of (fa ::: a). If (a :: Symbol), then we have a morphism from 
`DList f as` to a record where the field label is `a` and the field is `fa`
--}

data SomeK :: forall k ->  (k -> Type) -> Type where 
  SomeK :: forall k (a :: k) (c :: k -> Type)
        . c a -> SomeK k c 

-- something kinda like a dependent pair 
type (:::) :: forall k. (k -> Type) -> k -> Type
data (:::) f k where 
  (:::) :: forall k (f :: k -> Type) a. f a -> Sing (a :: k) -> f ::: a   

type Sigma k f = SomeK k ((:::) f) 

projSigma1 :: (forall (a :: k). Sing a -> r) -> Sigma k f -> r 
projSigma1 f (SomeK (fa ::: a)) = f a 

projSigma2 :: forall k f r. (forall (a :: k). f a -> r) -> Sigma k f -> r 
projSigma2 f (SomeK (fa ::: a)) = f fa 

type CPair k f c = SomeK k (Constrained f c)

type Constrained :: forall k. (k -> Type) -> (k -> Constraint) -> k -> Type 
data Constrained f c a where 
  Constrain :: forall k (a :: k) (c :: k -> Constraint) (f :: k -> Type)
             . c a => (f ::: a) -> Constrained f c a  

evince :: forall f c a. Constrained f c a -> Dict (c a)
evince (Constrain _) = Dict 

dsing :: f ::: a -> Sing a 
dsing (a ::: s) = s 

data DList' :: (k -> Type) -> [k] -> Type where 
  Nil :: forall k (c :: k -> Type) (a :: k).  DList' c '[]

  (:*) :: forall k (c :: k -> Type) (ks :: [k]) (k' :: k)
         . c ::: k' -> DList' c ks -> DList' c (k' ': ks)

data DList :: (k -> Type) -> NonEmpty k -> Type where 
  (:||) :: forall k (f :: k -> Type) (ks :: [k]) (a :: k) (b :: k) 
         . (f ::: a) -> DList' f ks -> DList f (a :| ks)

dpure :: (f ::: a) -> DList f (a :| '[])
dpure fa = fa :|| Nil   

dcons :: forall k (f :: k -> Type) (a :: k) (ks :: [k]) (b :: k) 
       . (f ::: a) -> DList f (b :| ks) -> DList f (a :| (b ': ks)) 
dcons fa (b :|| ks) = fa :|| (b :* ks)


dfold :: forall k (c :: k -> Type) (a :: k) (as :: [k]) b 
        . (forall (a :: k). c ::: a -> b -> b)
       -> b 
       -> DList c (a :| as)
       -> b 
dfold f b (a :|| as) = f a (go as)
  where 
    go :: forall (ks :: [k]). DList' c ks -> b 
    go = \case 
      Nil -> b
      ck :* rest -> f ck (go rest)   

type MkRow :: Type -> Row Type 
type family MkRow dlist where 
  MkRow (DList f (a :| as))  = Extend a (f a) (ToRow_ (DList' f as))

type ToRow_ :: Type -> Row Type 
type family ToRow_ dlist_ where 
  ToRow_ (DList' f '[]) = Empty 
  ToRow_ (DList' f (a ': as)) = Extend a (f a) (ToRow_ (DList' f as))

singLabel :: forall s. Sing (s :: Symbol) -> Label s 
singLabel s = Label @s 

dlistToRec :: forall 
              (f  :: Symbol -> Type) 
              (ss ::  [Symbol])
              (s  :: Symbol)
            . DList f (s :| ss)
           -> Rec (MkRow (DList f (s :| ss)))
dlistToRec ((fa ::: a) :|| as) = withKnownSymbol a $ R.extend (singLabel a) fa (go as) 
  where 
    go :: forall (as :: [Symbol]). DList' f as -> Rec (ToRow_ (DList' f as)) 
    go = \case 
      Nil -> R.empty 
      w@(fx ::: x) :* xs -> withKnownSymbol x $ R.extend (singLabel x) fx (go xs)





