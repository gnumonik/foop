{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Exists where



import Data.Kind
import Data.Constraint
import Data.Row
import Data.Row.Dictionaries
import qualified Data.Row.Records as R
import Data.Proxy

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

 
data Ex2 :: (k1 -> Constraint) -> (k2 -> Constraint) -> (k1 -> k2 -> Type) -> Type -> Type where 
  Ex2 :: forall k1 k2  
                (a  :: k1)
                (b  :: k2)
                (f  :: k1 -> k2 -> Type)
                (c1 :: k1 -> Constraint)
                (c2 :: k2 -> Constraint)
                (t :: Type)
       . (t ~ f a b, c1 a, c2 b) => f a b -> Ex2 c1 c2 f t  

data Ex2W :: (k1 -> Constraint) -> (k2 -> Constraint) -> (k1 -> k2 -> Type) -> Type -> Type where 
  Ex2W :: forall k1 k2  
                (a  :: k1)
                (b  :: k2)
                (f  :: k1 -> k2 -> Type)
                (c1 :: k1 -> Constraint)
                (c2 :: k2 -> Constraint)
                (t :: Type)
       . (t ~ f a b, c1 a, c2 b) =>  Ex2W c1 c2 f t

type Exists2 :: (k1 -> Constraint) -> (k2 -> Constraint) -> (k1 -> k2 -> Type) -> Type -> Constraint 
class Exists2 c1 c2 f t where 
  ex2 :: forall a b. (c1 a, c2 b, t ~ f a b) => f a b -> Ex2 c1 c2 f t 
  ex2 = Ex2 

  ex2W :: Ex2W c1 c2 f t 

instance (c1 a, c2 b) => Exists2 c1 c2 f (f a b) where 
  ex2W = Ex2W 

allHave :: forall f c children 
        . Forall children (Exists c f) 
       => Rec children 
       -> Rec (R.Map (Ex c f) children)
allHave = R.map @(Exists c f) go 
  where 
    go :: forall t 
        . Exists c f t 
       => t 
       -> Ex c f t 
    go t = case exW :: ExW c f t of 
      h@ExW -> Ex t 

allTransform :: forall c f g h children 
              . Forall children Unconstrained1 
             => Rec (R.Map (Deriving c f g) children)
             -> (forall x. c x => g x -> h x) 
             -> Rec (R.Map (Deriving c f h) children)
allTransform old f = R.transform' @children @(Deriving c f g) @(Deriving c f h) go old 
  where 
    go :: forall t. Deriving c f g t -> Deriving c f h t
    go mx = mx -/-> f 

allTo :: forall f g c children 
       .  Forall children (Exists c f) 
      => (forall a. c a => f a -> g a ) 
      -> Rec (R.Map (Ex c f ) children)
      -> Rec (R.Map (Deriving c f g) children)
allTo f = R.transform @(Exists c f) @children @(Ex c f) @(Deriving c f g) go 
  where 
    go :: forall t. Exists c f t => Ex c f t -> Deriving c f g t 
    go (Ex ft) = Deriving f (Ex ft)
