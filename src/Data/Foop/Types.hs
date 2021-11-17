{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RoleAnnotations, LiberalTypeSynonyms #-}
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
import Data.Singletons (KindOf)


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

  Observe :: (HasType l path deps, KnownSymbol l)
          => Label l 
          -> (TraceS path -> a)
          -> EntityF deps slots state query m a 

  Interact :: (HasType l path deps, KnownSymbol l)
          => Label l 
          -> (TraceE path -> a)
          -> EntityF deps slots state query m a 

  Query    :: Coyoneda query a -> EntityF deps slots state query m a

  GetSlot  :: SlotKey l slots slot 
           -> (StorageBox slot -> a) 
           -> EntityF deps slots state query m a

  Create   :: SlotKey l slots (Slot i su cs q)
           -> i
           -- probably going to need some kind of normalize constraint 
           -> Model r ds (Slot i su cs q)
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

data Model :: PathDir -> Row PathDir  -> SlotData -> Type where 
  Model :: forall root surface slots query state deps i
         . (SlotConstraint slots)
        =>  Spec root deps state (Slot i surface slots query)
        -> Model root deps (Slot i surface slots query)

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
type Spec :: PathDir -> Row PathDir -> Type -> SlotData -> Type 
data Spec root deps state slot where
  MkSpec :: forall state query deps surface slots i root .
   ( WellBehaved slots) => 
    { initialState   :: state 
    , handleQuery    :: AlgebraQ query :~> EntityM deps slots state query IO 
    , renderer       :: Renderer state surface 
    , slots          :: Proxy slots
    , dependencies   :: MkPaths  (Slot i surface slots query) deps 
    } -> Spec root deps state (Slot i surface slots query)

-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState ::  PathDir -> Row PathDir -> Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState  root deps slots surface st q where 
  EvalState :: (SlotConstraint slots) => {
      _entity      :: Spec root deps st (Slot i surface slots q)
    , _state       :: st
    , _storage     :: Rec (MkStorage slots)
    , _surface     :: surface 
    , _location    :: PathFinder' root 
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

class  RootOf path ~ root => Rooted root path 
instance RootOf path ~ root => Rooted root path   

data MkPaths :: SlotData -> Row PathDir -> Type where 
  MkPaths :: forall  slot paths 
           . (  Forall paths (Rooted slot))
           => Rec (R.Map (PathFinder 'Begin) paths )
           -> MkPaths slot paths  

  NoDeps :: forall  slot 
          . MkPaths  slot Empty  

type AllRooted slot deps = Forall deps (Rooted slot) 

data Extension :: PathDir -> SlotData -> PathDir -> Type where 
  MkExtension :: forall child parent
            . ExtendPath parent child
           => PathFinder 'Begin child -> Extension parent (RootOf child) child 

data Extension' :: PathDir -> PathDir -> Type where 
  MkExtension' :: Extension parent childRoot slot -> Extension' parent slot 

data Atlas :: PathDir ->  Row PathDir -> Type where 
  MkAtlas :: forall root slot paths deps. (AllExtend root deps) =>  Rec (R.Map (PathFinder 'Begin) deps) -> Atlas root deps 


data Crumbs a = Begin | Crumbs a :> a
infixl 1 :>
deriving instance Show a => Show (Crumbs a) 

data T a b c  
  = Branch_ (b := c)
  | Down_ a 
  | Leaf_ c 
  | Up_ c

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

type family Last (p :: PathDir) :: (T (Row SlotData) Symbol SlotData) where 
  Last (a :> b)   = b  

type family First (p :: PathDir) :: (T (Row SlotData) Symbol SlotData) where 
  First ('Begin :> a) = a 
  First (a :> b)      = First a 

type family LeafMe (t :: Trail) :: SlotData where 
  LeafMe ('Leaf_ slot) = slot 
  LeafMe ('Up_ slot) = slot 

type family HasLeaf (p :: PathDir) (s :: SlotData) :: Constraint where 
  HasLeaf ('Begin :> 'Leaf_ slot) slot = ()
  HasLeaf (old :> 'Leaf_ slot) slot   = ()

type family RootOf (p :: PathDir) :: SlotData where 
  RootOf p = LeafMe (First p)
{--
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

  Up  :: forall  parent l slot old1 i su cs q i' su' cs' q'
      .  -- (HasType l (Slot i su cs q) parent, KnownSymbol l) =>  
         Path  (old1 :> 'Leaf_ (Slot i su cs q))
      -> Path  (old1 :> 'Leaf_ (Slot i su cs q) :> Up_ (Slot i' su' cs' q'))
--}
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

type family JoinPath (p1 :: PathDir) (p2 :: PathDir) :: PathDir where 
  JoinPath (old :> 'Leaf_ (Slot i su cs q)) ('Begin :> 'Leaf_ (Slot i su cs q)) = (old :> 'Leaf_ (Slot i su cs q)) 

  JoinPath start (old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs :> 'Branch_ (l ':= Slot i' su' cs' q') :> 'Leaf_ (Slot i' su' cs' q'))
      = JoinPath start old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs :> 'Branch_ (l ':= Slot i' su' cs' q') :> 'Leaf_ (Slot i' su' cs' q')

  JoinPath start (old :> 'Leaf_ (Slot i su cs q) :> Up_ slot) = JoinPath start old :> 'Leaf_ (Slot i su cs q) :> Up_  slot

class -- Last (JoinPath p1 p2) ~ Last p2 =>  
  JoinPathC (p1 :: PathDir) (p2 :: PathDir) where 

  joinPath :: forall start
            . PathFinder start p1 
           -> PathFinder 'Begin p2 
           -> PathFinder start (JoinPath p1 p2)

instance JoinPathC (old :> 'Leaf_ (Slot i su cs q)) ('Begin :> 'Leaf_ (Slot i su cs q)) where 
  joinPath old Here = case old of 
    Here -> Here 
    Child i' pf -> Child i' pf 

instance ( JoinPathC start (old :> 'Leaf_ (Slot i su cs q))
         , JoinPath start (old ':> 'Leaf_ (Slot i su cs q)) ~ (JoinPath start old ':> 'Leaf_ (Slot i su cs q))) 
       => JoinPathC start (old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs :> 'Branch_ (l ':= Slot i' su' cs' q') :> 'Leaf_ (Slot i' su' cs' q')) where 
            joinPath old new = case new of 
              Child i rest -> Child i (joinPath old rest)

instance ( JoinPathC start (old :> 'Leaf_ slot' )
         , JoinPath start (old ':> 'Leaf_ slot' :> Up_ slot) ~ (JoinPath start old :> 'Leaf_ slot' :> Up_ slot)
         , JoinPath start (old ':> 'Leaf_ slot') ~ (JoinPath start old ':> 'Leaf_ slot')) 
        => JoinPathC start (old ':> 'Leaf_ slot' :> Up_ slot) where 
            joinPath old (Parent rest) = Parent (joinPath old rest)

class (JoinPathC parent child, FixPathC (JoinPath parent child)) => ExtendPath parent child where 
  extendPath :: PathFinder 'Begin parent -> PathFinder 'Begin child -> PathFinder' (FixPath (JoinPath parent child))
  extendPath p1 p2 = fixPath $ joinPath p1 p2 

instance (JoinPathC parent child, FixPathC (JoinPath parent child)) => ExtendPath parent child 

data PathFinder :: PathDir -> PathDir -> Type where 
  Here :: forall i su cs q start 
        . Ord i 
       => PathFinder start (start :> 'Leaf_ (Slot i su cs q))

  Child :: forall l q i su i' su' cs' q' cs root old start 
         . (ChildC l cs (Slot i' su' cs' q'), Ord i', Forall cs' SlotOrdC) 
        => i' 
        -> PathFinder start (old :> 'Leaf_ (Slot i su cs q)) 
        -> PathFinder start ( old 
                      :> 'Leaf_ (Slot i su cs q)
                      :> 'Down_ cs
                      :> 'Branch_ (l ':= Slot i' su' cs' q')
                      :> 'Leaf_ (Slot i' su' cs' q'))

  Parent :: forall start old slot slot' l cs 
          . PathFinder start (old :> 'Leaf_ slot)
         -> PathFinder start (old :> 'Leaf_ slot :> Up_  slot')
data HasA :: (k -> Constraint) -> (k -> Type) -> Type -> Type where 
  HasA :: forall k (a :: k) (f :: k -> Type) (c :: k -> Constraint) t  
       . (c a, t ~ f a) => f a -> HasA c f t  

type Has :: (k -> Constraint) -> (k -> Type) -> Type -> Constraint 
class Has c f t where 
  has :: (c a, t ~ f a) => f a -> HasA c f t
  has = HasA 

  unHas :: HasA c f t -> (forall a. f a ~ t => f a -> r) -> r 
  unHas (HasA x) f = f x 

instance c a => Has c f (f a)

instance HasDict (Has c f t) (HasA c f t) where 
  evidence (HasA x) = Dict 

class Evident (f :: k -> Type) (c :: k -> Constraint) where 
  withEvidence :: forall x r. f x -> (forall y. c y => f y -> r) -> r 

instance Evident (Extension' parent) (ExtendPath parent) where 
  withEvidence ex@(MkExtension' (MkExtension path)) f = f ex


newtype Wrapped :: (k -> Type) -> k -> Type where 
  Wrap :: f a -> Wrapped f a 

class Wraps (f :: k -> Type) (a :: k) where 
  wrap :: f a -> Wrapped f a 
  wrap = Wrap 

instance Wraps (f :: k -> Type) (a :: k)

type AllExtend root slots = Forall slots (ExtendPath root) 

type AllWrapped f slots = Forall slots (Wraps f)



type FixPath :: PathDir -> PathDir
type family FixPath path where 
  FixPath 'Begin = 'Begin 

  FixPath  ('Begin :> 'Leaf_ (Slot i su cs q)) = ('Begin :> 'Leaf_ (Slot i su cs q))

  FixPath (   old 
          :> 'Leaf_ (Slot i su cs q) 
          :> 'Down_ cs 
          :> 'Branch_ (l ':= slot')
          :> 'Leaf_ slot'
          :> 'Up_ _slot) = FixPath (old :> 'Leaf_ (Slot i su cs q))

  --FixPath 'Begin = 'Begin --stupid

  FixPath (      old 
             :> 'Leaf_ (Slot i su cs q)
             :> 'Down_ cs
             :> 'Branch_ (l ':= Slot i' su' cs' q' )
             :> 'Leaf_ (Slot i' su' cs' q')) = FixPath old 
                                            :> 'Leaf_ (Slot i su cs q)
                                            :> 'Down_ cs
                                            :> 'Branch_ (l ':= Slot i' su' cs' q' )
                                            :> 'Leaf_ (Slot i' su' cs' q')




class ValidatePath (FixPath path) => FixPathC path where 
  fixPath :: PathFinder 'Begin path -> PathFinder' (FixPath path )

instance FixPathC ('Begin :> 'Leaf_ (Slot i su cs q)) where
  fixPath Here = Here' 


instance ( FixPath (old ':> 'Leaf_ (Slot i su cs q)) ~ (FixPath old ':> 'Leaf_ (Slot i su cs q))
          , FixPathC (old :> 'Leaf_ (Slot i su cs q))
          )
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
                              :> 'Branch_ (l ':= slot )
                              :> 'Leaf_ slot
                              :> 'Up_  _slot
                 ) where 
                      fixPath (Parent rest) = case rest of 
                        Child i xs -> fixPath xs

class ValidatePath (p :: PathDir)
instance ValidatePath  ('Begin :> 'Leaf_ (Slot i su cs q))
instance ValidatePath (old :> 'Leaf_ (Slot i su cs q)) 
          => ValidatePath (  old 
                          :> 'Leaf_ (Slot i su cs q)
                          :> 'Down_ cs
                          :> 'Branch_ (l ':= Slot i' su' cs' q' )
                          :> 'Leaf_ (Slot i' su' cs' q'))

type OKPath :: PathDir -> Constraint 
type family OKPath path where 
  OKPath  ('Begin :> 'Leaf_ (Slot i su cs q)) = ()

  OKPath (      old 
             :> 'Leaf_ (Slot i su cs q)
             :> 'Down_ cs
             :> 'Branch_ (l ':= Slot i' su' cs' q' )
             :> 'Leaf_ (Slot i' su' cs' q')) = OKPath old 

{--
  OKPath (   old 
          :> 'Leaf_ (Slot i su cs q) 
          :> 'Down_ cs 
          :> 'Branch_ (l ':= slot)
          :> 'Leaf_ slot 
          :> 'Up_ (Slot i su cs q)) = OKPath old 


(||>) :: Path  old -> (Path old -> Path new) -> Path  new 
a ||> f = f a 
infixl 1 ||>
--}

(/>) :: NormalizedPath  old -> (NormalizedPath old -> NormalizedPath new) -> NormalizedPath  new 
a /> f = f a 
infixl 1 />

(+>) :: PathFinder start old -> (PathFinder start old -> PathFinder start new) -> PathFinder start new 
a +> b = b a 
infixl 1 +>

normalizePF :: forall path. PathFinder' path -> NormalizedPath path 
normalizePF = \case 
  Here' -> Start' 

  Child' i rest -> normalizePF rest /> Down' /> Branch' SlotKey /> Leaf' i

class (HasType l t rs, KnownSymbol l)   => HasType_ t rs l
instance (HasType l t rs,KnownSymbol l) => HasType_ t rs l

type HasTypeQ slot cs = DC.ForallV (HasType_ slot cs)

data NormalizedPath :: PathDir -> Type where 
  Start' :: forall l i q su cs
          . ( Ord i) 
           =>  NormalizedPath ('Begin :> 'Leaf_ (Slot i su cs q))

  Branch' :: forall l i q su cs slots old root 
         . ( KnownSymbol l
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

