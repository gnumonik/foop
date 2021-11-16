{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RoleAnnotations #-}
module Data.Foop.Types where
import Data.Kind
import GHC.TypeLits
import Data.Row
import qualified Data.Map as M
import Control.Monad.State.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Bifunctor ( Bifunctor(first, bimap) )
import Data.Functor.Coyoneda ( Coyoneda(..), liftCoyoneda )
import Data.Proxy
import Control.Comonad.Store
import Control.Concurrent.STM.TVar
import Control.Monad.Free.Church
import Data.Row.Internal ( Extend, Row(R), LT((:->)), FrontExtends (frontExtendsDict), FrontExtendsDict (FrontExtendsDict) )
import Data.Default
import qualified Data.Row.Records as R
import Data.Constraint
import qualified Data.Constraint.Forall as DC
import Control.Lens (Fold, to, Lens')
import Control.Lens.Getter
import Data.Type.Equality (type (:~:))
import Control.Concurrent.STM (TMVar)
import Data.Functor.Constant
import Data.Row.Dictionaries (IsA(..),As(..),ActsOn(..),As'(..))


{-- 

Ok so: 

The EntityF/EntityM free monad stuff only carries dependencies. It's slot is implicit 
(i.e. the Ord i constraint technically needs to be explicitly satisfied at *some point*)

Spec is the non-existentially-hidden configuration data type for an entity. The ord i constrain can still 
be implicit here. 

EvalState requires the path to be fully instantiated. Need some way of expressing the constraint that 
all of the dependency paths are satisfied. 

--}

------------
-- Types 
------------

-- | This is a kind; it only exists at the typelevel and its only purpose is 
-- to function as inputs to the type families which construct the render tree 
-- and the child entity storage 
type SlotData = (Type,Type,Type, Type -> Type)


-- | Slot index surface query
--   
--   Typelevel tuples realllllyyyyy suck syntactically so this 
--   synonym allows our users to avoid typing them out in type applications 
--   First argument will have to satisfy an Ord constraint but there's no way 
--   to express that here. 
type Slot :: Type -> Type -> Row SlotData -> (Type -> Type) ->  SlotData 
type Slot index surface children query = '(index,surface,RenderTree children,query)

-- | GADT which records the necessary Slot Data and functions as a kind of 
--   key for operations over child entities. It shouldn't ever be necessary for 
--   a user to manually construct this
data SlotKey :: Symbol -> Row SlotData -> SlotData -> Type where
  SlotKey :: (ChildC label slots slot, Forall slots SlotOrdC)  => SlotKey label slots slot

-- | The base functor for an entity. 
--
--   `slots` is a type of kind Row SlotData and records the data for the entity's children 
--
--   `state` is the entity's state type 
--
--   `query` is the ADT which represents the component's algebra 
--
--   `m` is the inner functor (which for now will always be IO)
type EntityF :: Row PathDir -> Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type
data EntityF deps slots state query m a where
  State   :: (state -> (a,state)) -> EntityF deps slots state query m a

  Lift    :: m a -> EntityF deps slots state query m a

  Observe :: Path path
          -> (TraceS path -> a)
          -> EntityF deps slots state query m a 

  Interact :: Path path
          -> (TraceE path -> a)
          -> EntityF deps slots state query m a 

  Query    :: Coyoneda query a -> EntityF deps slots state query m a

  GetSlot  :: SlotKey l slots slot 
           -> (StorageBox slot -> a) 
           -> EntityF deps slots state query m a

  Create   :: SlotKey l slots (Slot i su cs q)
           -> i
           -- probably going to need some kind of normalize constraint 
           -> Model r su cs q new i 
           -> a 
           -> EntityF deps slots state query m a

  Delete   :: SlotKey l slots '(i,su,RenderTree cs,q)
           -> i
           -> a 
           -> EntityF c slots state query m a

instance Functor m => Functor (EntityF location slots state query m) where
  fmap f =  \case
        State k          -> State (first f . k)
        Lift ma          -> Lift (f <$> ma)
        Observe path g   -> Observe path (fmap f g)
        Interact path g  -> Interact path (fmap f g) 
        Query qb         -> Query $ fmap f qb
        GetSlot key g    -> GetSlot key $ fmap f g -- (goChild f key g)
        Create s@SlotKey i e a -> Create s i e (f a)
        Delete key i a   -> Delete key i (f a)

-- | `EntityM` is the newtype wrapper over the (church-encoded) free monad
--   formed from the `EntityF` functor. 
--
--   `slots` is a type of kind Row SlotData and records the data for the entity's children 
--
--   `state` is the entity's state type 
--
--   `query` is the ADT which represents the entity's algebra 
--
--   `m` is the inner functor (which for now will always be IO)
newtype EntityM context slots state query m a = EntityM (F (EntityF context slots state query m) a) 
  deriving (Functor, Applicative, Monad)

instance Functor m => MonadState s (EntityM context slots s q m) where
  state f = EntityM . liftF . State $ f

instance  MonadIO m => MonadIO (EntityM context slots s q m) where
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM context slots s q ) where
  lift = EntityM . liftF . Lift


data BoxedContext :: (SlotData -> Constraint) -> Type where 
  BoxedContext :: (c context, SlotOrdC context)=> RenderLeaf context -> BoxedContext c 

data TBoxedContext :: (SlotData -> Constraint) -> Type where 
  TBoxedContext :: (c (Slot i su cs q), SlotOrdC (Slot i su cs q)) => TVar (RenderLeaf (Slot i su cs q)) -> TBoxedContext c 

type MkNode surface children = Rec ("surface"  .== surface 
                                  .+ "children" .== RenderTree children)
{--}
type RenderTree :: Row SlotData -> Type 
newtype RenderTree slots where 
  MkRenderTree :: Rec (R.Map RenderBranch slots)
               -> RenderTree slots 

instance Show (Rec (R.Map RenderBranch slots)) => Show (RenderTree slots) where 
  show (MkRenderTree m) = "MkRenderTree " <> show m

type RenderBranch :: SlotData -> Type 
newtype RenderBranch slot where 
  MkRenderBranch :: M.Map (Indexed slot) (RenderLeaf slot) 
               -> RenderBranch slot 

instance Show (M.Map (Indexed slot) (RenderLeaf slot)) => Show (RenderBranch slot) where 
  show (MkRenderBranch slot) = "MkRenderBranch " <> show slot 

type RenderLeaf :: SlotData -> Type 
data RenderLeaf slot where 
  MkRenderLeaf :: forall surface children i q
               . surface 
              -> RenderTree children 
              -> RenderLeaf '(i,surface,RenderTree children,q)

instance (Show surface, Show (RenderTree children)) 
      => Show (RenderLeaf (Slot i surface children q)) where 
  show (MkRenderLeaf su cs) = "MkRenderLeaf " <> show su <> show cs 

{--
-- | `Prototype` is an existential wrapper for `Spec` which hides 
--   the spec's state and slot types. Only the surface (i.e. the type which the state renders to)
--   and the query algebra are exposed.
data Prototype :: Type -> Row SlotData -> (Type -> Type) -> SlotData -> Type where
  Prototype :: (SlotConstraint slots, SlotOrdC context)
            => Spec slots surface  state query context
            -> Prototype surface slots query context 
--}

data Model :: PathDir -> Type -> Row SlotData -> (Type -> Type) -> Row PathDir -> Type -> Type where 
  Model :: forall root surface slots query state loc i
         . (SlotConstraint slots)
        =>  Spec root slots surface state query loc i
        -> Model root surface slots query loc i 

-- | `~>` is a type synonym for natural transformations (generally between functors
--   but that constraint can't be expressed here).
--
--   m ~> n == forall a. m a -> n a
type (~>) m n = (forall a. m a -> n a)

-- | `NT` is a GADT which holds a natural transformation. (See `~>`)
--
--   This mainly exists to help with type inference.
data NT :: (Type -> Type) -> (Type -> Type) -> Type where
  NT :: forall m n. (forall a. m a -> n a) -> NT m n

-- | Infix synonym for `NT`
type (:~>) m n = NT m n

type Renderer :: Type -> Type -> Type 
data Renderer  state surface where 
  MkRenderer :: {
    render    :: state -> surface 
  , onRender  :: surface -> IO ()
  } -> Renderer state surface 

newtype Handler query state slots loc 
  = Handler {
      runHandler 
      :: forall r. ((forall x. query x -> EntityM loc slots state query IO x) -> r) -> r}

-- | A `Spec` is the GADT from which an Entity is constructed. 
type Spec :: PathDir -> Row SlotData -> Type -> Type -> (Type -> Type) -> Row PathDir -> Type -> Type
data Spec root slots surface state query c  i where
  MkSpec ::
   ( WellBehaved slots) => 
    { initialState   :: state 
    , handleQuery    :: AlgebraQ query :~> EntityM deps slots state query IO 
    , renderer       :: Renderer state surface 
    , slots          :: Proxy slots
    , dependencies   :: Atlassed root (Slot i surface slots query) deps 
    } -> Spec root slots surface state query deps i  

-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)



-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState ::  PathDir -> Row PathDir -> Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState  root deps slots surface st q where 
  EvalState :: (SlotConstraint slots) => {
      _entity      :: Spec root slots surface st q deps i
    , _state       :: st
    , _storage     :: Rec (MkStorage slots)
    , _surface     :: surface 
    , _location    :: Path root 
    , _environment :: TMVar (Entity (RootOf root)) -- maybe not
  } -> EvalState root deps slots surface st q 

-- | Existential wrapper over the EvalState record. 
data ExEvalState :: PathDir -> Row PathDir -> Type -> Row SlotData -> (Type -> Type) -> Type where
  ExEvalState :: ( SlotConstraint slots) 
              => EvalState  root deps slots surface st query 
              -> ExEvalState root deps surface slots query  

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   make type signatures far more readable. 
data Transformer root loc surface slots query where 
   Transformer :: 
     (forall x. query x -> IO (x,ExEvalState root loc surface slots query)) -> Transformer root loc surface slots query 

-- | `EntityStore surface query` == `Store (ExEvalState surface query) (Transformer surface query)`
-- 
--   Since I bet you're not all "wow what this does is so amazingly clear from the type!": 
--   
--   `Store s a` is isomorphic to `(s,s -> a)`. (ExEvalState surface query) contains the state of an entity. A transformer is a 
--   function from a query in the entity's algebra to (modulo IO) a tuple containing the result of that query and 
--   the entity's new state. 
-- 
--   So our entity store has the rough shape (modulo IO): `Store s (q x -> (x,s))`
--   
--   and *that* is isomorphic to (s, s -> q x -> (x,s)).  Which should look sorta-kinda-almost-just-a-little like 
--   a State Monad. And, indeed, the main point of an EntityStore is that it gives us state-monad-like 
--   functionality *combined* with comonad-functionality: We can extract the state. 
-- 
--   But mainly this is what it is because Store is my favorite comonad and I jump at any chance to use it :) 
type EntityStore ::  PathDir -> Row PathDir -> Type -> Row SlotData -> (Type -> Type) -> Type 
type EntityStore root loc surface children query = Store (ExEvalState root loc surface children query) (Transformer root loc surface children query)

-- | `Entity surface query` is a newtype wrapper over `TVar (EntityStore surface query)`
--   Mainly for making type signatures easier.
type Entity :: SlotData -> Type 
data Entity slot where 
  Entity :: (SlotOrdC '(i,su,RenderTree cs,q)) 
         => TVar (EntityStore root loc su cs q) -> Entity '(i,su,RenderTree cs,q)

-- | `Tell query` ==  `() -> query ()` 
type Tell query = () -> query ()

-- | `Request query a` == `(a -> a) -> query a` 
type Request query a = (a -> a) -> query a 

-- don't export the constructor 
-- | `Object surface query` == `Object (Entity surface query)`
--
--   This is a wrapper for a "root" Entity (i.e an Entity which is not the child of any other)
type Object :: SlotData -> Type
data Object slot where 
   Object :: Entity '((),su,cs,q) -> Object '((),su,cs,q)

---------------------------
-- Families and constraints 
---------------------------

type IndexOf :: SlotData -> Type
type family IndexOf slotData where 
  IndexOf '(i,s,cs,q) = i

unIndexed :: Indexed '(i,su,cs,q)
          -> i 
unIndexed (Indexed Index i) = i 

data Index :: SlotData -> Type -> Type where 
  Index :: Ord i => Index '(i,s,cs,q) i 

instance Show i => Show (Indexed (Slot i s cs q)) where 
  show (Indexed Index i) = show i 

data Indexed :: SlotData ->  Type where 
  Indexed :: Index slot i -> i -> Indexed slot  

instance Eq (Indexed slot) where 
  (Indexed Index i) == (Indexed Index i') = i == i' 

instance Ord (Indexed slot ) where 
  (Indexed Index i) <= (Indexed Index i') = i <= i' 

type Index' :: SlotData -> Type 
type family Index' slotData where 
  Index' '(i,s,cs,q) = Index '(i,s,cs,q) i

type QueryOf_ :: SlotData -> (Type -> Type) 
type family QueryOf_ slot where 
  QueryOf_ '(i,su,cs,q) = q 

class QueryOf_ slot  ~ q => QueryOf (slot :: SlotData) (q :: Type -> Type)
instance QueryOf_ slot ~ q => QueryOf slot q 

type SurfaceOf_ :: SlotData -> Type 
type family SurfaceOf_ slot where 
  SurfaceOf_ '(i,su,cs,q) = su 

type OfSurface_ :: Type -> SlotData -> Constraint 
type family OfSurface_ su slot  where 
  OfSurface_ su (Slot i su cs q) = ()

class (SurfaceOf_ slot ~ su, OfSurface_ su slot)    => SurfaceOf slot su 
instance (SurfaceOf_ slot ~ su, OfSurface_ su slot) => SurfaceOf slot su 

type ChildrenOf :: SlotData -> Row SlotData 
type family ChildrenOf slot where 
  ChildrenOf (Slot i su cs q)=  cs 


-- | The first argument to SlotData must satisfy an Ord constraint
type ChildStorage :: Row SlotData -> Type
type ChildStorage slots = Rec (MkStorage slots)

newtype StorageBox :: SlotData -> Type where 
  MkStorageBox :: M.Map (Indexed slot) (Entity slot) 
               -> StorageBox slot

-- | Constructs a storage record from a row of slotdata.
type MkStorage :: Row SlotData -> Row Type
type family MkStorage slotData  where
  MkStorage slotData = R.Map StorageBox slotData 

type family SlotC (slot :: SlotData) :: Constraint where 
  SlotC '(i,s,RenderTree cs,q) = (Ord i, Forall cs SlotOrdC)

class (SlotC slot, Ord (IndexOf slot))  => SlotOrdC slot where 
  slotOrd :: Dict (Ord (IndexOf slot))
  slotOrd = Dict 

instance (SlotC slot, Ord (IndexOf slot)) => SlotOrdC slot 

-- | Compound constraint which a child entity must satisfy. You should probably just look at the source.
type ChildC :: Symbol -> Row SlotData -> SlotData -> Constraint
type family ChildC label slots slot where
  ChildC label slots slot 
      = ( HasType label slot slots   
        , Forall slots SlotOrdC
        , SlotOrdC slot 
        , KnownSymbol label)

type MkRender :: Row SlotData -> Type
type family MkRender slots where
  MkRender slots = RenderTree slots 

type SlotConstraint slots = ( Forall slots SlotOrdC 
                            , WellBehaved slots 
                            , AllUniqueLabels (R.Map Proxy slots)
                            , Forall (R.Map Proxy slots) Default)

type Top :: forall k. k -> Constraint 
class Top (a :: k)
instance Top (a :: k)

-- no way this is gonna work

class (a => b) => Implies a b where 
  impl :: a :- b 

instance (a => b) => Implies a b where 
  impl = Sub Dict 

class (forall a. Implies (c1 a) (c2 a)) => Entails c1 c2 where 
  derive :: forall a. c1 a :- c2 a 
  derive = Sub Dict 

instance (forall a. Implies (c1 a) (c2 a)) => Entails c1 c2 

testEntailment :: forall c1 c2 a. (Entails c1 c2, c1 a) => Dict (c2 a)
testEntailment = mapDict (derive @c1 @c2 @a) Dict  

------ *really* don't want this stuff to be here but need it in scope 

data (:=) a b = a := b deriving (Show, Eq)
infixr 8 := 


data Rooted :: PathDir -> SlotData -> PathDir -> Type where 
  MkRooted :: forall root path
            . Compatible root path 
           => Path path -> Rooted root (RootOf path) path 

data Atlassed :: PathDir -> SlotData -> Row PathDir -> Type where 
  MkAtlassed :: Rec (R.Map (Rooted root slot) paths) -> Atlassed root slot paths 
             
data Atlas :: SlotData -> [PathDir] -> Type where 
  FirstPath :: forall path. Path path -> Atlas (RootOf path) '[path]
  AddPath :: forall slot path paths 
           . RootOf path ~ slot 
          => Path path 
          -> Atlas slot paths 
          -> Atlas slot (path ': paths) 

data Crumbs a = Begin | Crumbs a :> a
infixl 1 :>
deriving instance Show a => Show (Crumbs a) 

data T a b c  
  = Branch_ (b := c)
  | Down_ a 
  | Leaf_ c 
  | Up_ a b c 

type PathDir = Crumbs (T (Row SlotData) Symbol SlotData)

type Trail = (T (Row SlotData) Symbol SlotData)

type StorageTree :: Row SlotData -> Type 
data StorageTree slots where 
  MkStorageTree :: Rec (R.Map StorageBox slots) -> StorageTree slots 

type TraceS :: PathDir -> Type 
type family TraceS crumbs where 
  TraceS ('Begin :> 'Leaf_ t)        = RenderLeaf t 
  TraceS (old :> 'Leaf_ t)           = RenderLeaf t 
  TraceS (old :> 'Branch_ (l ':= t)) = RenderBranch t 
  TraceS (old :> 'Down_ t)           = RenderTree t 

type TraceE :: PathDir -> Type 
type family TraceE crumbs where 
  TraceE ('Begin :> 'Leaf_ t)        = Entity t 
  TraceE (old :> 'Leaf_ t)           = Entity t 
  TraceE (old :> 'Branch_ (l ':= t)) = StorageBox t
  TraceE (old :> 'Down_ t)           = StorageTree t  


type NormalizeF :: PathDir -> PathDir 
type family NormalizeF path where

  NormalizeF (old1 :>  'Leaf_ (Slot i su cs q) :> 'Down_ cs :> 'Branch_ (l ':= slot) :> 'Leaf_ slot :> 'Up_ cs l slot)
    = NormalizeF old1 :> 'Leaf_ (Slot i su cs q)

  NormalizeF ('Begin :> 'Leaf_ l)
    = ('Begin :> 'Leaf_ l)

  NormalizeF (old1 :> 'Down_ cs) 
    = NormalizeF old1 :> 'Down_ cs

  NormalizeF (old1 :> old2 :> 'Leaf_ l)    
    = NormalizeF  (old1 :> old2):> 'Leaf_ l 

  NormalizeF (old1 :> old2 :> 'Branch_ b) 
    = NormalizeF (old1 :> old2) :> 'Branch_ b 


class  ( Normalized (NormalizeF p) , 
         RootOf p ~ RootOf (NormalizeF p)) => 
  Normalize (p :: PathDir)  where 
  normalize ::  Path p -> NormalizedPath (NormalizeF p)

instance Normalize ('Begin :> 'Leaf_ (Slot i su cs q)) where 
  normalize Start  = Start' 

instance  (Normalize old, RootOf (old :> 'Down_ cs) ~ RootOf (NormalizeF (old :> 'Down_ cs)))
 => Normalize (old :> 'Down_ cs) where 
  normalize (Down path) = case path of 
    Start -> Down' Start' 
    l@(Leaf i path) -> Down' $ normalize @old l

instance (  Normalize (old1 :> 'Leaf_ (Slot i su cs q))
          , NormalizeF (old1 ':> 'Leaf_ (Slot i su cs q)) ~ (NormalizeF old1 ':> 'Leaf_ (Slot i su cs q))
          , HasType l slot cs
          , KnownSymbol l) 
          =>  Normalize (old1 :> 'Leaf_ (Slot i su cs q) :>  'Down_ cs :> 'Branch_ (l ':= slot) :> 'Leaf_ slot :> 'Up_ cs l slot) 
  where 
    normalize (Up (Leaf _ (Branch (Down x)))) = normalize x

instance ( Normalize (old1 :> old2)
         , Normalized (NormalizeF (old1 :> old2 :> 'Leaf_ l))
         , RootOf (old1 :> old2) ~ RootOf (NormalizeF (old1 :> old2) :> 'Leaf_ l)
         ) 
        => Normalize (old1 :> old2 :> 'Leaf_ l) where 
  normalize (Leaf i p)  = case p of  
    b@(Branch _) -> Leaf' i (normalize b)

-- might be sketchy
instance ( Normalize old1 
         , Normalized (NormalizeF (old1 :> 'Branch_ b))
         , RootOf (old1 :> 'Branch_ b) ~ RootOf (NormalizeF (old1 :> 'Branch_ b))) => Normalize (old1 :> 'Branch_ b) where 
  normalize (Branch  p) = Branch' SlotKey (normalize p)

class Normalized (p :: PathDir)
-- instance Normalized 'Begin 
instance Normalized ('Begin :> 'Leaf_ l)
instance (Normalized (old1 :> old2 )) => Normalized (old1 :> old2 :> 'Leaf_ l)
instance (Normalized old) => Normalized (old :> 'Branch_ b)
instance Normalized old => Normalized (old :> 'Down_ b)

type family Last (p :: PathDir) :: (T (Row SlotData) Symbol SlotData) where 
  Last (a :> b)   = b  

type family First (p :: PathDir) :: (T (Row SlotData) Symbol SlotData) where 
  First ('Begin :> a) = a 
  First (a :> b)      = First a 

type Connected :: PathDir -> PathDir -> PathDir 
type family Connected p1 p2 where 
  Connected (old :> 'Leaf_ slot) ('Begin :> 'Leaf_ slot)
    =  (old :> 'Leaf_ slot)

  Connected old (new1 :> new2)
    = Connected old new1 :> new2 

type family LeafMe (t :: Trail) :: SlotData where 
  LeafMe ('Leaf_ slot) = slot 

type TestPath = 'Begin :> 'Leaf_ (Slot Int Int Empty Maybe)

data ElCompat :: PathDir -> LT PathDir -> [LT PathDir] -> Type where 
  ElC1 :: (Compatible root k, KnownSymbol l) => ElCompat root (l ':-> k) '[l ':-> k]
  ElCS :: (Compatible root x, KnownSymbol l) => ElCompat root (l' ':-> old) ((l' ':-> old) ': lts) -> ElCompat root (l ':-> x) (l ':-> x ': l' ':-> old ': lts)

elLabel :: forall root l p ps
         . ElCompat root (l ':-> p) ps
        -> Label l 
elLabel = \case 
  ElC1 -> Label @l 
  ElCS old -> Label @l

type ElC :: PathDir -> LT PathDir -> [LT PathDir] -> Constraint 
class ElC root path paths where 
  el :: ElCompat root path paths  

instance (Compatible root path, KnownSymbol l) => ElC root (l ':-> path) '[l ':-> path] where 
  el = ElC1
instance {-# OVERLAPS #-} (ElC root (l' ':-> old) (l' ':-> old ': paths), Compatible root new, KnownSymbol l) => ElC root (l ':-> new) (l ':-> new ': l' ':-> old ': paths) where 
  el = ElCS $ el @root @(l' ':-> old) @(l' ':-> old ': paths) 

type family Head (xs :: [k]) :: k where 
  Head (x ': xs) = x 

class ElC root (Head paths) paths => DeriveCompatible root paths where 
  deriveCompatible :: ElCompat root (Head paths) paths   
  deriveCompatible = el

type family MapR_ (f :: a -> b) (r :: [LT a]) :: [LT b] where
  MapR_ f '[l :-> v] = '[l :-> f v]
  MapR_ f (l :-> v ': t) = l :-> f v ': MapR_ f t


type Hm root = IsA (Compatible root) Path 

elToRec :: forall root l p ps ps'  
         . ( KnownSymbol l 
           , ElC root (l ':-> p) (l ':-> p ': ps)
           , Mapped Path ps' (l ':-> p ': ps)
           , AllUniqueLabels (R (l ':-> p ': ps))
           ) 
        => NormalizedPath root 
        -> Rec (R ps')
        -> Rec (R.Map (ConstBox root) (R (l ':-> p ': ps)) )
elToRec npath r = undefined  
  where 
    hmbam = undefined -- (ana (Label @l) (transmute  @Path  @ps' @(l ':-> p ': ps) r) el)
{--
    ana :: forall l p ps row
         . (PopRec l p  (l ':-> p ': ps) ps)
        => Label l 
        -> MapBox Path (R (l ':-> p ': ps) )
        -> ElCompat root (l ':-> p) (l ':-> p ': ps) 
        -> (MapBox Path (R ps), ConstBox p p)
    ana l (MapBox paths) = \case 
      ElC1 -> case paths R..! l of 
        p -> (EmptyBox,ConstBox (Constant (MkCompatiBox npath p)) )
      ElCS rest -> case popEm @l @(Path p) paths of 
--}
    cata :: (Rec ('R (MapR_ Path ps)), ConstBox root p) -> Rec ('R ((l ':-> ConstBox root p) : MapR_ (ConstBox root) ps))
    cata = undefined 

instance ElC root (Head paths) paths => DeriveCompatible root paths

class  UnfoldRec (c :: k -> Constraint) (f :: k -> Type) (row :: [LT Type])  where 
  unfoldRec :: Proxy c -> Rec (R row) -> UnconsRec (R row) (UnconsBox c f) -- (f t, Rec (R ts))
  --unconsRec aRec = (aRec R..! (Label @l), aRec R..- (Label @l))

type UnconsRec ::  Row Type -> (Maybe (LT Type) -> Row Type -> Type) -> Type 
type family UnconsRec row f where 
  UnconsRec (R '[]) k = k 'Nothing (R '[])
  UnconsRec (R (l ':-> f a ': as)) k = k ('Just (l ':-> f a)) (R as)

data UnconsBox :: (k -> Constraint) -> (k -> Type) -> Maybe (LT Type) -> Row Type -> Type where 
  DJust :: forall k (a :: k) (c :: k -> Constraint) (f :: k -> Type) l (as ::  [LT Type]) 
         . (UnfoldRec c f as, c a,  KnownSymbol l) => Rec (R (l ':-> f a ': as)) -> UnconsBox c f ('Just (l ':-> f a)) (R as)
  DNothing :: UnconsBox c f 'Nothing  (R '[])

unboxCons :: forall k (f :: k -> Type) (c :: k -> Constraint) (a :: k) (rt :: [LT Type]) r l  
           . UnconsBox c f ('Just (l ':-> f a))  (R rt)
          -> ((UnfoldRec c f rt, KnownSymbol l, c a) => Label l -> f a -> Rec (R rt) -> r)
          -> r 
unboxCons d@(DJust aRec) f = f lbl (aRec R..! lbl) (aRec R..- lbl)
  where 
    lbl = getLbl d 

    getLbl :: forall c f l x rx. UnconsBox c f ('Just (l ':-> x)) rx -> Label l 
    getLbl (DJust _)= Label @l

class TransformRec (c :: k -> Constraint) (f :: k -> Type) (g :: k -> Type) (r1 :: Row Type) (r2 :: Row Type) where 
  transformRec :: Proxy c -> (forall x. c x => f x -> g x) -> Rec r1 -> Rec r2  

instance ( UnfoldRec c f '[l ':-> f a]
         , UnfoldRec c g '[l ':-> g a] 
         , UnconsRec (R '[l ':-> f a]) (UnconsBox c f) ~ UnconsBox c f ('Just (l ':-> f a)) (R '[])
         , UnconsRec (R '[l ':-> g a]) (UnconsBox c g) ~ UnconsBox c g ('Just (l ':-> g a)) (R '[])
         ) => TransformRec c f g (R '[l ':-> f a]) (R '[l ':-> g a])  where 
                transformRec Proxy f r1 = case unfoldRec (Proxy @c) r1 of 
                  consbox -> unboxCons consbox $ \lbl fa _ -> lbl .== f fa
{--
instance ( UnfoldRec c f (l ':-> f a ': r1)
         , UnfoldRec c g (l ':-> g a ': r2 )
         , UnconsRec (R (l ':-> f a ': r1)) (UnconsBox c f) ~ UnconsBox c f ('Just (l ':-> f a)) (R r1) 
         , UnconsRec (R (l ':-> g a ': r2)) (UnconsBox c g) ~ UnconsBox c g ('Just (l ':-> g a)) (R r2) 
         , TransformRec c f g (R r1) (R r2)
         , FoldRec c l a f g r2
         ) => TransformRec c f g (R (l ':-> f a ': r1)) (R (l ':-> g a ': r2 )) where 
                transformRec proxy f rx = case unfoldRec (Proxy @c) rx of 
                  box@(DJust rest) -> unboxCons box $ \lbl fa rest ->  case transformRec proxy f rest :: Rec (R r2) of 
--}




class ( KnownSymbol l
      , FrontExtends l (g a) (R ys)
      , c a
      , AllUniqueLabels (Extend l (g a) (R ys))
      ) => FoldRec (c :: k -> Constraint) (l :: Symbol) (a :: k) (f :: k -> Type) (g :: k -> Type) (ys :: [LT Type]) where 
  type Folded l g a ys :: Row Type 
  type Folded l g a ys = Extend l (g a) (R ys)

  foldRec :: c a => Label l -> f a -> (forall x. c x => f x -> g x) -> Rec (R ys) -> Rec (Extend l (g a) (R ys))
  foldRec lbl fa f r = R.extend lbl (f fa) r

instance (KnownSymbol l, c a) => FoldRec c l a f g '[]

instance ( KnownSymbol l
      , FrontExtends l (g a) (R (y ': ys))
      , c a
      , AllUniqueLabels (Extend l (g a) (R (y ': ys)))
      ) => FoldRec c l a f g (y ': ys)

-- instance TransformRec 

foldRecC :: forall c f g l a ts
         . (KnownSymbol l
         , FrontExtends l (f a) (R ts)
         , AllUniqueLabels (Extend l (f a) (R ts)))
        => Label l 
        -> f a 
        -> Rec (R ts)
        -> Rec (Extend l (f a) (R ts))
foldRecC lbl@Label fa rts =  undefined 

instance UnfoldRec c f '[] where 
  unfoldRec _ _ = DNothing 


instance ( HasType l (f t) (R row)
      , c t 
      , KnownSymbol l 
      , row ~ '[l ':-> f t]
      , R '[] ~ (R row R..- l )
      , FrontExtends l (f t) (R '[]))
      => UnfoldRec c f '[l ':-> f t]  where
          unfoldRec proxy myRec = DJust myRec 

instance ( HasType l (f t) (R row)
      , KnownSymbol l 
      , row ~ (l ':-> f t ': ts)
      , c t
      , R ts ~ (R row R..- l )
      , FrontExtends l (f t) (R ts)
      , UnfoldRec c f ts)
      => UnfoldRec c f (l ':-> f t ': ts) where
          unfoldRec _ myRec = DJust myRec  


data MapBox :: (PathDir -> Type) -> Row PathDir -> Type where
  EmptyBox :: forall f. MapBox f Empty 
  MapBox :: Rec (R.Map f row) -> MapBox f row 

class R lts ~ R.Map f (R lks) => Mapped (f :: PathDir -> Type) (lts :: [LT Type]) (lks :: [LT PathDir]) where 
  transmute ::  Rec (R lts) -> MapBox f (R lks )

instance Mapped f '[] '[] where 
  transmute = const EmptyBox 

instance Mapped f '[l ':-> f a] '[l ':-> a] where 
  transmute = MapBox 

instance {-# OVERLAPS #-} (Mapped f lts lks) => Mapped f (l ':-> f a ': lts) (l ':-> a ': lks) where 
  transmute = MapBox 


type AllCompat :: PathDir -> [PathDir] -> Constraint 
class  AllCompat r ps where 
  --allCompat :: forall p. El p ps => Dict 

newtype ConstBox root r = ConstBox (Constant (CompatiBox root) r)


data CompatiBox :: PathDir -> Type where 
  MkCompatiBox :: forall root child rootSlot
                . (Compatible root child, rootSlot ~ RootOf root) 
               => NormalizedPath root 
               -> Path child
           --    -> TMVar (Entity (RootOf root))
               -> CompatiBox child 
{--
-- need the proxy
withCompatiBox :: forall child r
                . CompatiBox child 
               -> (forall root rootSlot. Compatible root child => NormalizedPath root -> TMVar (Entity rootSlot) -> r)
               -> r 
withCompatiBox (MkCompatiBox path tmv) f = f path tmv 
--}
class Compatible l1 r1 => Compatible2 l1 r1 where 
  compatible :: Dict (Compatible l1 r1)
  compatible = Dict 

instance Compatible l1 r1 => Compatible2 l1 r1


type Compatible :: PathDir -> PathDir -> Constraint 
class ( TipR r1 ~ TipLR l1 r1
      , Connection l1 r1 ~ Connected l1 r1 
      , Normalize (Connection l1 r1)
      , RootL l1 ~ RootLR l1 r1) => Compatible l1 r1 where 
    
    type Connection l1 r1 :: PathDir 
    type Connection l1 r1 = Connected l1 r1 
    
    type RootL l1 :: SlotData 
    type RootL l1 = LeafMe (First l1) 

    type RootLR l1 r1 :: SlotData 
    type RootLR l1 r1 = LeafMe (First (Connected l1 r1))

    type TipR r1 :: Trail 
    type TipR r1 = Last r1

    type TipLR l1 r1 :: Trail 
    type TipLR l1 r1 = Last (Connected l1 r1)

    connectAndNormalize :: Path l1 -> Path r1 -> NormalizedPath (NormalizeF (Connected l1 r1))
    connectAndNormalize x y = normalize $ connectEm x y

    connectEm :: Path  l1 -> Path  r1  -> Path  (Connected l1 r1) 


instance Normalize (old :> 'Leaf_ slot) 
  => Compatible (old :> 'Leaf_ slot) ('Begin :> 'Leaf_ slot) where 
    connectEm old Start = case old of 
      Leaf i older -> Leaf i older 
      Start        -> Start 

instance ( Normalize (Connected old1  (new1 :> new2 :> 'Leaf_ slot))
      --   , Last (Connected old1  (new1 :> new2 :> 'Leaf_ slot)) ~ 'Leaf_ slot
         , Compatible old1 (new1 :> new2)
         , Connected old1 (new1 :> new2 :> 'Leaf_ slot) ~ (Connected old1 (new1 :> new2) :> 'Leaf_ slot )
         , RootOf (Connected old1 (new1 :> new2 :> 'Leaf_ slot)) ~ RootOf old1
    --     , RootR (new1 :> new2)  ~ RootR (new1 :> new2 :> 'Leaf_ slot)
         ) => Compatible old1 (new1 :> new2 :> 'Leaf_ slot) where 
                connectEm old (Leaf i rest) = Leaf i (connectEm @old1 @(new1 :> new2) old rest) 

instance ( Normalize (Connected old1 (new1 :> 'Branch_ b))
         , Compatible old1 new1 
         , Connected old1 (new1 :> 'Branch_ b) ~ (Connected old1 new1 :> 'Branch_ b)
         , RootOf (Connected old1 (new1 :> 'Branch_ b)) ~ RootOf old1 )  
        => Compatible old1 (new1 :> 'Branch_ b) where 
            connectEm old (Branch rest) = Branch $ connectEm @old1 @new1 old rest 

instance ( Normalize (Connected old1 (new1 :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs))

         , Compatible old1 (new1 :> 'Leaf_ (Slot i su cs q))

         , Connected old1 (new1 :> 'Leaf_ (Slot i su cs q)) ~   (Connected old1 new1 :> 'Leaf_ (Slot i su cs q))

         , RootL old1 ~ RootLR old1 (new1 :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs)
        )  
        => Compatible old1 (new1 :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
            connectEm old (Down rest) =  Down $ connectEm  old rest 

instance ( Normalize (Connected old1 (new1 :> 'Leaf_ slot :> 'Up_ cs l slot))

         , Compatible old1 (new1 :> 'Leaf_ slot)

         , Connected old1 (new1 :> 'Leaf_ slot) ~   (Connected old1 new1 :> 'Leaf_ slot)

         , RootL old1 ~ RootLR old1 (new1 :> 'Leaf_ slot :> 'Up_ cs l slot)
        ) => Compatible old1 (new1 :> 'Leaf_ slot :> 'Up_ cs l slot) where 
            connectEm old (Up rest) = Up $ connectEm old rest   




type family HasLeaf (p :: PathDir) (s :: SlotData) :: Constraint where 
  HasLeaf ('Begin :> 'Leaf_ slot) slot = ()
  HasLeaf (old :> 'Leaf_ slot) slot   = ()

type family GetLeaf (p :: PathDir) :: SlotData where 
  GetLeaf ('Begin :> 'Leaf_ slot) = slot 
  GetLeaf (old :> 'Leaf_ slot) = slot   

type family RootOf (p :: PathDir) :: SlotData where 
  RootOf p = LeafMe (First p)

data Path ::  PathDir -> Type where 
  Start :: forall i su cs q l . (Ord i) =>  Path ('Begin :> 'Leaf_ (Slot i su cs q))

  Branch :: forall l i q su slots cs root old 
          . (ChildC l slots (Slot i su cs q), Ord i, Forall slots SlotOrdC) 
        => Path (old :> 'Down_ slots) 
        -> Path ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q))

  Leaf :: forall l q i su cs  slots old root 
        . Ord i 
       => i
       -> Path (old :> 'Branch_ (l ':= Slot i su cs q))
       -> Path ((old :> 'Branch_ (l ':= Slot i su cs q)) :> 'Leaf_ (Slot i su cs q))

  Down :: forall i su cs q root old 
        . Path (old :> 'Leaf_ (Slot i su cs q)) 
       -> Path (old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs)

  Up  :: forall  parent l slot old1 i su cs q 
      .  (HasType l (Slot i su cs q) parent, KnownSymbol l)
      =>  Path  (old1 :> 'Leaf_ (Slot i su cs q))
      -> Path  (old1 :> 'Leaf_ (Slot i su cs q) :> Up_ parent l (Slot i su cs q))

data PathFinder' :: PathDir -> Type where 
  Here' :: forall i su cs q l 
        . Ord i 
       =>  PathFinder' ('Begin :> 'Leaf_ (Slot i su cs q))

  -- downward leaf to leaf 
  Child' :: forall l q i su i' su' cs' q' cs root old
         . (ChildC l cs (Slot i' su' cs' q'), Ord i', Forall cs' SlotOrdC) 
        => i' 
        -> PathFinder' (old :> 'Leaf_ (Slot i su cs q)) 
        -> PathFinder' (  old 
                      :> 'Leaf_ (Slot i su cs q)
                      :> 'Down_ cs
                      :> 'Branch_ (l ':= Slot i' su' cs' q' )
                      :> 'Leaf_ (Slot i' su' cs' q'))
{--
  Parent' :: forall l i su cs q i' su' cs' q'  old 
          . HasType l (Slot i' su' cs' q') cs  
         => PathFinder' (old  :> 'Leaf_ (Slot i su cs q)) 
         -> PathFinder' ( old 
                      :> 'Leaf_ (Slot i su cs q) 
                      :> 'Down_ cs 
                      :> 'Branch_ (l ':= Slot i' su' cs' q')
                      :> 'Leaf_ (Slot i' su' cs' q'))
         -> PathFinder' (  old :> 'Leaf_ (Slot i su cs q) )
--}


data PathFinder :: PathDir -> Type where 
  Here :: forall i su cs q 
        . Ord i 
       => PathFinder ('Begin :> 'Leaf_ (Slot i su cs q))

  Child :: forall l q i su i' su' cs' q' cs root old
         . (ChildC l cs (Slot i' su' cs' q'), Ord i', Forall cs' SlotOrdC) 
        => i' 
        -> PathFinder (old :> 'Leaf_ (Slot i su cs q)) 
        -> PathFinder (  old 
                      :> 'Leaf_ (Slot i su cs q)
                      :> 'Down_ cs
                      :> 'Branch_ (l ':= Slot i' su' cs' q')
                      :> 'Leaf_ (Slot i' su' cs' q'))

  Parent :: forall slot old l cs 
          . PathFinder (old :> 'Leaf_ slot)
         -> PathFinder (old :> 'Leaf_ slot :> Up_ cs l slot)


type FixPath :: PathDir -> PathDir
type family FixPath path where 
  FixPath 'Begin = 'Begin --stupid 
  
  FixPath  ('Begin :> 'Leaf_ (Slot i su cs q)) = ('Begin :> 'Leaf_ (Slot i su cs q))

  FixPath (      old 
             :> 'Leaf_ (Slot i su cs q)
             :> 'Down_ cs
             :> 'Branch_ (l ':= Slot i' su' cs' q' )
             :> 'Leaf_ (Slot i' su' cs' q')) = FixPath old 
                                            :> 'Leaf_ (Slot i su cs q)
                                            :> 'Down_ cs
                                            :> 'Branch_ (l ':= Slot i' su' cs' q' )
                                            :> 'Leaf_ (Slot i' su' cs' q')

  FixPath (   old 
          :> 'Leaf_ (Slot i su cs q) 
          :> 'Down_ cs 
          :> 'Branch_ (l ':= Slot i' su' cs' q')
          :> 'Leaf_ (Slot i' su' cs' q')
          :> 'Up_ _cs _l (Slot i' su' cs' q')) = FixPath old :> 'Leaf_ (Slot i su cs q)

class Fixed path ~ FixPath path => FixPathC path where 
  type Fixed path :: PathDir 
  type Fixed path = FixPath path 

  fixPath :: PathFinder path -> PathFinder' (FixPath path )

instance FixPathC ('Begin :> 'Leaf_ (Slot i su cs q)) where
  fixPath Here = Here' 

instance (FixPath (old ':> 'Leaf_ (Slot i su cs q))
         ~ (FixPath old ':> 'Leaf_ (Slot i su cs q))
         , FixPathC (old :> 'Leaf_ (Slot i su cs q)))
     => FixPathC ( old 
                 :> 'Leaf_ (Slot i su cs q)
                 :> 'Down_ cs
                 :> 'Branch_ (l ':= Slot i' su' cs' q' )
                 :> 'Leaf_ (Slot i' su' cs' q')) where 
                   fixPath (Child i rest) = Child' i (fixPath rest)


instance ( FixPathC (old :> 'Leaf_ (Slot i su cs q))
         , FixPath (old ':> 'Leaf_ (Slot i su cs q)) ~ (FixPath old ':> 'Leaf_ (Slot i su cs q))
                 ) => FixPathC ( old
                              :> 'Leaf_ (Slot i su cs q)
                              :> 'Down_ cs
                              :> 'Branch_ (l ':= Slot i' su' cs' q' )
                              :> 'Leaf_ (Slot i' su' cs' q')
                              :> 'Up_ _cs _l (Slot  i' su' cs' q')
                 ) where 
                      fixPath (Parent rest) = case rest of 
                        Child i xs -> fixPath xs


type OKPath :: PathDir -> Constraint 
type family OKPath path where 
  OKPath  ('Begin :> 'Leaf_ (Slot i su cs q)) = ()

  OKPath (      old 
             :> 'Leaf_ (Slot i su cs q)
             :> 'Down_ cs
             :> 'Branch_ (l ':= Slot i' su' cs' q' )
             :> 'Leaf_ (Slot i' su' cs' q')) = OKPath old 


  OKPath (   old 
          :> 'Leaf_ (Slot i su cs q) 
          :> 'Down_ cs 
          :> 'Branch_ (l ':= slot)
          :> 'Leaf_ slot 

          :> 'Up_ cs l slot) = OKPath old 

(||>) :: Path  old -> (Path old -> Path new) -> Path  new 
a ||> f = f a 
infixl 1 ||>
(/>) :: NormalizedPath  old -> (NormalizedPath old -> NormalizedPath new) -> NormalizedPath  new 
a /> f = f a 
infixl 1 />

(+>) :: PathFinder old -> (PathFinder old -> PathFinder new) -> PathFinder new 
a +> b = b a 
infixl 1 +>
normalizePF :: forall path. PathFinder' path -> NormalizedPath path 
normalizePF = \case 
  Here' -> Start' 

  Child' i rest -> normalizePF rest /> Down' /> Branch' SlotKey /> Leaf' i

  -- Parent' rest -> normalizePF rest 

class (HasType l t rs, KnownSymbol l)   => HasType_ t rs l
instance (HasType l t rs,KnownSymbol l) => HasType_ t rs l

type HasTypeQ slot cs = DC.ForallV (HasType_ slot cs)

data NormalizedPath :: PathDir -> Type where 
  Start' :: forall l i q su cs
          . ( Ord i
            , Normalized ('Begin :> 'Leaf_ (Slot i su cs q))) 
           =>  NormalizedPath ('Begin :> 'Leaf_ (Slot i su cs q))

  Branch' :: forall l i q su cs slots old root 
         . (KnownSymbol l
           , HasType l (Slot i su cs q) slots
           , Ord i) 
        => SlotKey l slots (Slot i su cs q) 
        -> NormalizedPath  (old :> 'Down_ slots) 
        -> NormalizedPath  ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q))

  Leaf' :: forall q i su cs l slots old root 
        . (Ord i)
       => i
       -> NormalizedPath  (old :> 'Branch_ (l ':= Slot i su cs q))
       -> NormalizedPath  ((old :> 'Branch_ (l ':= Slot i su cs q)) :> 'Leaf_ (Slot i su cs q))

  Down' :: forall i su cs q old root 
         . NormalizedPath (old :> 'Leaf_ (Slot i su cs q))
         -> NormalizedPath (old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs)



{-- 
• Could not deduce: LeafMe (First (NormalizeF old1 ':> old2))
                    ~ LeafMe (First (NormalizeF (old1 ':> old2)))
    arising from the superclasses of an instance declaration
  from the context: (Normalize old1, Normalize (old1 ':> old2),
                     Normalized
                       ((NormalizeF old1 ':> old2) ':> 'Leaf_ (Slot i su cs q)))
    bound by the instance declaration
    at /home/gsh/code/haskell/foop/src/Data/Foop/Types.hs:(516,12)-(519,146)
  NB: ‘LeafMe’ is a non-injective type family
• In the instance declaration for
    ‘Normalize
       ((((((old1 ':> old2) ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs)
          ':> 'Branch_ (l ':= slot))
         ':> 'Leaf_ slot)
        ':> 'Up_ (Slot i su cs q))’
  --}

