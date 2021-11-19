{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Exists where



import Data.Kind
import Data.Constraint

-- (adapted from IsA in Data.Row.Dictionaries)
-- HasA c f t == exists a. c a => f a 
-- (more or less)
data Ex :: (k -> Constraint) -> (k -> Type) -> Type -> Type where 
  Ex :: forall k 
                (a :: k) 
                (f :: k -> Type) 
                (c :: k -> Constraint) 
                t 
       . ( c a
         , t ~ f a
         ) => f a -> Ex c f t

-- Having both the witness and the wrapper type is useful 
data ExW :: (k -> Constraint) -> (k -> Type) -> Type -> Type where 
  ExW :: forall k (a :: k) (f :: k -> Type) (c :: k -> Constraint) t 
       . (c a, t ~ f a) => ExW c f t

-- | Slight variation of IsA from Data.Row.Dictionaries 
--   From one angle this is a way to existentially bind type variables
--   + (more importantly) discharge them 
--  
--   From another angle, this lets create a constraint which asserts that
--   some Row k is ~ R.Map f k (and that c a holds)
--   (This is useful because we take a Rec (R.Map f row) as input 
--   during the construction of a Model, and GHC is really bad at 
--   inferring the `row` part of that. This + the constraint solver fixes that)
type Exists :: (k -> Constraint) -> (k -> Type) -> Type -> Constraint 
class  Exists c f t where 
  ex :: forall a. (c a, t ~ f a) => f a -> Ex c f t
  ex = Ex

  exW :: ExW c f t 

  exElim :: Ex c f t -> (forall a. (t ~ f a, c a) => f a -> r) -> r 
  exElim (Ex x) f = f x 

-- really a shame there's no way to sneak the c a constraint into the class 
-- cuz life would be so much easier w/ c a as a superclass 
instance c a => Exists c f (f a) where 
  exW = ExW 

-- HasA c f t is sufficient evidence for membership in the Has c f t class 
instance HasDict (Exists c f t) (Ex c f t) where 
  evidence (Ex x) = Dict 

data Deriving :: (k -> Constraint) ->  (k -> Type) -> (k -> Type) -> Type -> Type where 
  Deriving :: forall k 
                 (f :: k -> Type)
                 (g :: k -> Type)
                 (c :: k -> Constraint)
                 t 
         . (forall (x :: k). c x => f x -> g x)
        -> Ex c f t 
        -> Deriving c f g t


exImpl :: Deriving c f g t
         -> (forall (x :: k). c x => g x -> h x)
         -> Deriving c f h t
exImpl mx@(Deriving f (Ex ft)) g = Deriving (g . f) (Ex ft)

(-/->) = exImpl  

discharge :: forall c f g t r
           . Deriving c f g t
          -> (forall a. (f a ~ t,c a) => g a -> r)
          -> r 
discharge  (Deriving f (Ex ft)) g = g (f ft)