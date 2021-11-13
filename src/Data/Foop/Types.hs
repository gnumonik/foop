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
import Data.Row.Internal ( Extend, Row(R), LT((:->)) )
import Data.Default
import qualified Data.Row.Records as R
import Data.Constraint
import qualified Data.Constraint.Forall as DC
import Control.Lens (Fold, to, Lens')
import Control.Lens.Getter
import Data.Type.Equality (type (:~:))
import Control.Concurrent.STM (TMVar)
import Data.Functor.Constant

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
           -> Model su cs q new
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

data Model :: Type -> Row SlotData -> (Type -> Type) -> Row PathDir -> Type where 
  Model :: forall surface slots query state loc 
         . (SlotConstraint slots)
        =>  Spec slots surface state query loc
        -> Model surface slots query loc

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
type Spec :: Row SlotData -> Type -> Type -> (Type -> Type) -> Row PathDir -> Type
data Spec slots surface state query c where
  MkSpec ::
   ( WellBehaved slots, Ord i) => 
    { initialState   :: state 
    , handleQuery    :: AlgebraQ query :~> EntityM loc slots state query IO 
    , renderer       :: Renderer state surface 
    , slots          :: Proxy slots
    , dependencies   :: Atlassed (Slot i surface slots query) o
    } -> Spec slots surface state query loc

-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)



-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState ::  Row PathDir -> Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState  loc slots surface st q where 
  EvalState :: (SlotConstraint slots, Ord i) => {
      _entity      :: Spec slots surface st q loc 
    , _state       :: st
    , _storage     :: Rec (MkStorage slots)
    , _surface     :: surface 
  --  , _location    :: Path loc
  --  , _environment :: CompatiBox loc -- maybe not
  } -> EvalState loc slots surface st q 

-- | Existential wrapper over the EvalState record. 
data ExEvalState :: SlotData ->  Row PathDir -> Type -> Row SlotData -> (Type -> Type) -> Type where
  ExEvalState :: ( SlotConstraint slots, Ord i) 
              => EvalState  loc slots surface st q
              -> ExEvalState root loc surface slots q

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   make type signatures far more readable. 
data Transformer root loc surface slots query where 
   Transformer :: (Ord i) => 
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
type EntityStore ::  SlotData -> Row PathDir -> Type -> Row SlotData -> (Type -> Type) -> Type 
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

data Rooted :: SlotData -> PathDir -> Type where 
  MkRooted :: Path path -> Rooted (RootOf path) path 

data Atlassed :: SlotData -> Row PathDir -> Type where 
  MkAtlassed :: Rec (R.Map (Rooted slot) paths) -> Atlassed slot paths 
             
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
  TraceE ('Begin :> 'Leaf_ t)         = Entity t 
  TraceE (old :> 'Leaf_ t)           = Entity t 
  TraceE (old :> 'Branch_ (l ':= t)) = StorageBox t
  TraceE (old :> 'Down_ t)           = StorageTree t  


type NormalizeF :: PathDir -> PathDir 
type family NormalizeF path where
  NormalizeF ('Begin :> 'Leaf_ l)
    = ('Begin :> 'Leaf_ l)

  NormalizeF (old1 :> 'Down_ cs) 
    = NormalizeF old1 :> 'Down_ cs

  NormalizeF (old1 :> 'Down_ cs :> 'Branch_ (l ':= slot) :> 'Leaf_ slot :> 'Up_ slot) 
    = NormalizeF  (old1 :>  'Down_ cs) 

  NormalizeF (old1 :> old2 :> 'Leaf_ l)    
    = NormalizeF  (old1 :> old2):> 'Leaf_ l 

  NormalizeF (old1 :> old2 :> 'Branch_ b) 
    = NormalizeF (old1 :> old2) :> 'Branch_ b 

class  ( Normalized (NormalizeF p)
       , RootOf p ~ RootOf (NormalizeF p)) => 
  Normalize (p :: PathDir)  where 
  normalize ::  Path p -> NormalizedPath (NormalizeF p)

instance Normalize ('Begin :> 'Leaf_ (Slot i su cs q)) where 
  normalize Start  = Start' 

instance  (Normalize old, RootOf (old :> 'Down_ cs) ~ RootOf (NormalizeF (old :> 'Down_ cs)))
 => Normalize (old :> 'Down_ cs) where 
  normalize (Down path) = case path of 
    Start -> Down' Start' 
    l@(Leaf i path) -> Down' $ normalize @old l

instance (Normalize (old :> 'Down_ cs)
        , RootOf (old :> 'Down_ cs) ~ RootOf (old :> 'Down_ cs :> 'Branch_ (l ':= slot))) 
      => Normalize (old :> 'Down_ cs :> 'Branch_ (l ':= slot) :> 'Leaf_ slot :> 'Up_ slot ) 
  where 
    normalize (Up (Leaf i (Branch  d@(Down d')))) = normalize d 

instance ( Normalized (NormalizeF (old1 :> old2 :> 'Leaf_ l))
         , Normalize (old1 :> old2)
         , RootOf (old1 :> old2) ~ RootOf (NormalizeF (old1 :> old2 :> 'Leaf_ l))) 
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

data EleC :: PathDir -> k -> [k] -> Type where 
  El1 :: Compatible root k => EleC root k '[k]
  El2 :: Compatible root x => EleC k ks -> EleC k (x ': ks)

type El :: k  -> [k] -> Constraint 
class El k ks where 
  el :: Ele k ks 

instance El a '[a] where 
  el = El1
instance {-# OVERLAPS #-} El a as => El a (x ': as) where 
  el = El2 el  


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

instance ( Normalize (Connected old1 (new1 :> 'Leaf_ slot :> 'Up_ slot))

         , Compatible old1 (new1 :> 'Leaf_ slot)

         , Connected old1 (new1 :> 'Leaf_ slot) ~   (Connected old1 new1 :> 'Leaf_ slot)

         , RootL old1 ~ RootLR old1 (new1 :> 'Leaf_ slot :> 'Up_ slot)
        ) => Compatible old1 (new1 :> 'Leaf_ slot :> 'Up_ slot) where 
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

  Up  :: forall  slot root old1 slots 
      .  Path  (old1 :> 'Leaf_ slot)
      -> Path  (old1 :> 'Leaf_ slot :> Up_ slot)

class (HasType l t rs, KnownSymbol l)   => HasType_ t rs l
instance (HasType l t rs,KnownSymbol l) => HasType_ t rs l

type HasTypeQ slot cs = DC.ForallV (HasType_ slot cs)

data NormalizedPath :: PathDir -> Type where 
  Start' :: forall l i q su cs. (Ord i) =>  NormalizedPath ('Begin :> 'Leaf_ (Slot i su cs q))

  Branch' :: forall l i q su cs slots old root 
         . (KnownSymbol l, HasType l (Slot i su cs q) slots, Ord i) 
        => SlotKey l slots (Slot i su cs q) 
        -> NormalizedPath  (old :> 'Down_ slots) 
        -> NormalizedPath  ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q))

  Leaf' :: forall q i su cs l slots old root 
        . Ord i 
       => i
       -> NormalizedPath  (old :> 'Branch_ (l ':= Slot i su cs q))
       -> NormalizedPath  ((old :> 'Branch_ (l ':= Slot i su cs q)) :> 'Leaf_ (Slot i su cs q))

  Down' :: forall i su cs q old root 
         . NormalizedPath (old :> 'Leaf_ (Slot i su cs q))
         -> NormalizedPath (old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs)



{-- 
extendify :: ( Connectable old ('Leaf_ (Slot i su cs q)) ('Begin :> 'Leaf_ (Slot i su cs q)) 
             , Normalize (Connected (old :> 'Leaf_ (Slot i su cs q)) ('Begin :> 'Leaf_ (Slot i su cs q)))
             , Normalize (Connected 
                          (Connected (old :> 'Leaf_ (Slot i su cs q)) ('Begin :> 'Leaf_ (Slot i su cs q)))
                          (path :> target)
                          )
             )
          => Path root (old :> 'Leaf_ (Slot i su cs q)) 
          -> Path (Slot i su cs q) (path :> target)
          -> Targets root target 
extendify root new = case connect' root new of 
  
  • Could not deduce: Connected
                      old1 (new1 ':> 'Leaf_ (Slot i su cs q))
                    ~ (old0 ':> 'Leaf_ (Slot i0 su0 cs q0))
  from the context: (Normalize
                       (Connected
                          old1 ((new1 ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs)),
                     Compatible old1 (new1 ':> 'Leaf_ (Slot i su cs q)),
                     Last (Connected old1 (new1 ':> 'Leaf_ (Slot i su cs q)))
                     ~ 'Leaf_ (Slot i su cs q),
                     Connected old1 ((new1 ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs)
                     ~ (Connected old1 (new1 ':> 'Leaf_ (Slot i su cs q))
                        ':> 'Down_ cs))
    bound by the instance declaration
    at /home/gsh/code/haskell/foop/src/Data/Foop/Types.hs:(573,10)-(581,73)
  Expected type: Path
                   (Connected old1 ((new1 ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs))
    Actual type: Path
                   ((old0 ':> 'Leaf_ (Slot i0 su0 cs q0)) ':> 'Down_ cs)
  The type variables ‘old0’, ‘i0’, ‘su0’, ‘q0’ are ambiguous
• In the expression:
    Down $ connectEm @old1 @(new1 :> 'Leaf_ (Slot i su cs q)) old rest
  In an equation for ‘connectEm’:
      connectEm old (Down rest)
        = Down
            $ connectEm @old1 @(new1 :> 'Leaf_ (Slot i su cs q)) old rest
  In the instance declaration for
    ‘Compatible
       old1 ((new1 ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs)’
• Relevant bindings include
    old :: Path old1
      (bound at /home/gsh/code/haskell/foop/src/Data/Foop/Types.hs:582:23)
    connectEm :: Path old1
                 -> Path ((new1 ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs)
                 -> Path
                      (Connected old1 ((new1 ':> 'Leaf_ (Slot i su cs q)) ':> 'Down_ cs))
      (bound at /home/gsh/code/haskell/foop/src/Data/Foop/Types.hs:582:13)
  --}

