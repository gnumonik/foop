{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Exists where



import Data.Kind
import Data.Constraint
import Data.Row
import Data.Row.Dictionaries
import qualified Data.Row.Records as R
import Data.Proxy
import Data.Type.Equality (type (:~:) (Refl))
import Data.Void 
import Data.Row.Internal 
import GHC.TypeLits (Symbol)

-- it's prettier than "Unconstrained1"

type Top :: forall k. k -> Constraint 
class Top k 
instance Top k 

-- we're gonna need lists bleh 
-- most of this is taken/adapted from Data.SOP.Constraint 
-- (which is a cool library with absolutely godawful names for everything)
-- main difference is instead of a "fold" for the class method, 
-- I'm just associating a dictionary w/ instances 

type family
  AllF (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  AllF _c '[]       = ()
  AllF  c (x ': xs) = (c x, Each c xs)


class (AllF c xs, Each Top xs) => Each (c :: k -> Constraint) (xs :: [k]) where
  allDict :: forall t ts. xs :~: (t ': ts) -> (Dict ( c t), Dict (Each c ts))
  allDict Refl = (Dict,Dict)  

instance Each c '[]
instance (c a, Each c as) => Each c (a ': as)

-- not really similar to fmap
type family FMap (f :: k -> Type) (xs :: [k]) :: [Type] where 
  FMap f '[] = '[]
  FMap f (x ': xs) = f x ': FMap f xs 

emapEmpty :: forall xs ys f. (xs ~ '[], ys ~ FMap f xs) => ys :~: '[]
emapEmpty = Refl 

class Each (Exists Top f) xs => AllEx1 f xs 
instance Each (Exists Top f) xs => AllEx1 f xs 

--  for (g :: (k -> Type) -> [k] -> [Type] -> Type), (f :: k -> Type), (c :: k -> Constraint), (t :: Type)
--  there exists some (xs :: [k]) such that (for every (x :: k) in (xs :: [k]), there exists some a such that tx ~ f a & c a)
--    and 
--  t ~ g f xs (FMap f xs)
-- i think this actually does what i want but man it's unwieldy 
data EachHas ::  ((k -> Type) -> [k] -> [Type] -> Type) -> (k -> Type) -> (k -> Constraint) -> Type -> Type where
  EachHas    :: forall k 
             (xs :: [k])
             (c :: k -> Constraint) 
             (f :: k -> Type)
             (g :: (k -> Type) -> [k] -> [Type] -> Type)
             (t :: Type)
           . (Exists (Each (Exists c f)) (g f xs) t
           , t ~ g f xs (FMap f xs) ) 
           => g f xs (FMap f xs) -> EachHas g f c t 

data FMapped :: (k -> Type) -> [k] -> [Type] -> Type where 
  FMapped :: forall f ks ts. ts ~ FMap f ks => FMapped f ks ts 

data EachHasW ::  ((k -> Type) -> [k] -> [Type] -> Type) -> (k -> Type) -> (k -> Constraint) -> Type -> Type where
  EachHasW    :: forall k 
             (xs :: [k])
             (c :: k -> Constraint) 
             (f :: k -> Type)
             (g :: (k -> Type) -> [k] -> [Type] -> Type)
             (t :: Type)
           . (Exists (Each (Exists c f)) (g f xs) t
           , t ~ g f xs (FMap f xs) ) => EachHasW g f c t  

type EachHasC :: ((k -> Type) -> [k] -> [Type] -> Type) -> (k -> Type) -> (k -> Constraint) -> Type -> Constraint 
class EachHasC g f c t where 
  eachHasW :: forall xs.  EachHasW g f c t 

instance ( Exists (Each (Exists c f)) (g f xs) (g f xs (FMap f xs))
         , t ~ FMap f xs)
        => EachHasC g f c (g f xs t) where 
  eachHasW =  EachHasW :: EachHasW g f c (g f xs t)

{-- 
class Each (Exists c f) xs => AxEy xs f c where 
  mapAll :: 
--}


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


data Mapped :: (k -> Constraint) -> (k -> Type) -> Row k -> Row Type -> Type where 
  Mapped :: forall k 
            (c :: k -> Constraint) 
            (f :: k -> Type)
            (rt :: Row Type)  
            (row :: Row k)
          . ( Forall rt (Exists c f) 
            , rt ~ R.Map f row) 
          => Mapped c f row rt 

type  MappedC :: (k -> Constraint) -> (k -> Type) -> Row k -> Row Type -> Constraint 
class MappedC c f rk rt where 
  mapped :: Mapped c f rk rt 

instance ( Forall rt (Exists c f)
         , rt ~ R.Map f rk) => MappedC c f rk rt where 
  mapped = Mapped 





