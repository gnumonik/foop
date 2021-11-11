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
type EntityF :: PathDir -> Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type
data EntityF loc slots state query m a where
  State   :: (state -> (a,state)) -> EntityF loc slots state query m a

  Lift    :: m a -> EntityF c slots state query m a

  Observe ::  CompatibleC (Slot i su slots query) loc path
          =>  Path (Slot i su slots query) path
          -> (TraceS path -> a)
          -> EntityF loc slots state query m a 

  Interact :: CompatibleC (Slot i su slots query) loc path 
          =>  Path (Slot i su slots query) path
          -> (TraceE path -> a)
          -> EntityF loc slots state query m a 

  Query    :: Coyoneda query a -> EntityF deps slots state query m a

  GetSlot  :: SlotKey l slots slot 
           -> (StorageBox slot -> a) 
           -> EntityF c slots state query m a

  Create   :: SlotKey l slots (Slot i su cs q)
           -> i
           -- probably going to need some kind of normalize constraint 
           -> Model su cs q new
           -> a 
           -> EntityF (loc :> 'Leaf_ (Slot i2 su2 slots query)) slots state query m a

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

data Model :: Type -> Row SlotData -> (Type -> Type) -> PathDir -> Type where 
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
type Spec :: Row SlotData -> Type -> Type -> (Type -> Type) -> PathDir -> Type
data Spec slots surface state query c where
  MkSpec ::
   ( WellBehaved slots) => 
    { initialState   :: state 
    , handleQuery    :: AlgebraQ query :~> EntityM loc slots state query IO 
    , renderer       :: Renderer state surface 
    , slots          :: Proxy slots
    } -> Spec slots surface state query loc

-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)

-- | Constrained query handler
type QHandler :: (Type -> Type) -> PathDir -> Row SlotData -> Type ->  Type 
data QHandler query loc slots state  where 
  MkQHandler :: forall query state slots loc.
                (query ~>  EntityM loc slots state query IO)
             -> QHandler query loc slots state 



-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: SlotData -> PathDir -> Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState root loc slots surface st q where 
  EvalState :: ( SlotConstraint slots) => {
      _entity      :: Spec slots surface st q loc
    , _state       :: st
    , _storage     :: Rec (MkStorage slots)
    , _surface     :: surface 
    , _location    :: Path root (loc :> 'Leaf_ (Slot i surface slots q))
    , _environment :: TMVar (Entity root) -- maybe not
  } -> EvalState root loc slots surface st q 

-- | Existential wrapper over the EvalState record. 
data ExEvalState :: SlotData ->  PathDir -> Type -> Row SlotData -> (Type -> Type) -> Type where
  ExEvalState :: EvalState root loc slots surface st q
              -> ExEvalState root loc surface slots q

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   make type signatures far more readable. 
newtype Transformer root loc surface slots query = Transformer {transform :: forall x. query x -> IO (x,ExEvalState root loc surface slots query)}

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
type EntityStore ::  SlotData -> PathDir -> Type -> Row SlotData -> (Type -> Type) -> Type 
type EntityStore root loc surface children query = Store (ExEvalState root loc surface children query) (Transformer root loc surface children query)

-- | `Entity surface query` is a newtype wrapper over `TVar (EntityStore surface query)`
--  
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

type ChildrenOf_ :: SlotData -> Type 
type family ChildrenOf_ slot where 
  ChildrenOf_ '(i,su,RenderTree cs,q) = RenderTree cs 

-- this one's different, if shit breaks that's why
class ChildrenOf_ slot ~ RenderTree cs => ChildrenOf slot cs 
instance ChildrenOf_ slot ~ RenderTree cs => ChildrenOf slot cs 


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


data Atlas :: SlotData -> [PathDir] -> Type where 
  Empty :: forall su cs q i. Atlas (Slot i su cs q) '[]
  AddPath :: forall su cs q path paths i
           . Path (Slot i su cs q) path 
          -> Atlas (Slot i su cs q) paths 
          -> Atlas (Slot i su cs q) (path ': paths) 


data Crumbs a = Begin a | Crumbs a :> a
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
  TraceS ('Begin ('Leaf_ t))         = RenderLeaf t 
  TraceS (old :> 'Leaf_ t)           = RenderLeaf t 
  TraceS (old :> 'Branch_ (l ':= t)) = RenderBranch t 
  TraceS (old :> 'Down_ t)           = RenderTree t 

type TraceE :: PathDir -> Type 
type family TraceE crumbs where 
  TraceE ('Begin ('Leaf_ t))         = Entity t 
  TraceE (old :> 'Leaf_ t)           = Entity t 
  TraceE (old :> 'Branch_ (l ':= t)) = StorageBox t
  TraceE (old :> 'Down_ t)           = StorageTree t  

type Connect :: PathDir -> Symbol ->  PathDir -> PathDir 
type family Connect crumbs1 l crumbs2 where 
  Connect ('Begin ('Leaf_ slot)) l ('Begin ('Leaf_ slot)) = 'Begin ('Leaf_ slot) 
  Connect (old :> 'Leaf_ slot) l ('Begin ('Leaf_ slot)) = old :> 'Leaf_ slot 
  Connect (old :> 'Leaf_ slot) l (left :> rest) = Connect (old :> 'Leaf_ slot) l left :> rest 

type NormalizeF :: PathDir -> PathDir 
type family NormalizeF path where
  NormalizeF ('Begin ('Leaf_ l)) 
    = ('Begin ('Leaf_ l))

  NormalizeF (old :> 'Down_ cs) 
    = (NormalizeF old :> 'Down_ cs)

  NormalizeF (old :> 'Down_ cs :> 'Branch_ (l ':= slot) :> 'Leaf_ slot :> 'Up_ slot) 
    = NormalizeF  (old :> 'Down_ cs) 

  NormalizeF (old :> 'Leaf_ l)    
    = NormalizeF  old :> 'Leaf_ l 

  NormalizeF (old :> 'Branch_ b) 
    = NormalizeF old :> 'Branch_ b 

class -- Normalized (NormalizeF p) => 
  Normalize (p :: PathDir)  where 
  normalize :: forall root. Path root p -> NormalizedPath root (NormalizeF p)

instance Normalize ('Begin ('Leaf_ slot)) where 
  normalize Start  = Start' 

instance Normalize ('Begin ('Leaf_ (Slot i su cs q)) :> 'Down_ cs ) where 
  normalize (Down Start) = Down1 Start' 

instance Normalize old
        => Normalize (old :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
  normalize (Down (Leaf i p)) = Down2 (Leaf' i $ normalize p) 

instance Normalize (old :> 'Down_ cs ) 
      => Normalize (old :> 'Down_ cs :> 'Branch_ (l ':= slot) :> 'Leaf_ slot :> 'Up_ slot ) 
  where 
    normalize (Up (Leaf i (Branch  d@(Down d')))) = normalize d 

instance ( Normalized (NormalizeF (old1 :> old2 :> 'Leaf_ l))
         , Normalize (old1 :> old2)) 
        => Normalize (old1 :> old2 :> 'Leaf_ l) where 
  normalize p  = case p of  
    Leaf i p -> Leaf' i (normalize p)

instance Normalize old => Normalize (old :> 'Branch_ b) where 
  normalize (Branch  p) = Branch' SlotKey (normalize p)

class Normalized (p :: PathDir)
-- instance Normalized 'Begin 
instance Normalized ('Begin ('Leaf_ l))
instance Normalized (old1 :> old2 ) => Normalized (old1 :> old2 :> 'Leaf_ l)
instance Normalized old => Normalized (old :> 'Branch_ b)
instance Normalized old => Normalized (old :> 'Down_ b)

type family Last (p :: PathDir) :: (T (Row SlotData) Symbol SlotData) where 
  Last ('Begin t) = t 
  Last (a :> b)   = b  
{--
type ConnectableF :: PathDir -> Symbol -> PathDir -> Constraint 
class ConnectableF p1 l  p2

instance ( KnownSymbol l
        , HasType l slot cs) => ConnectableF (old :> 'Leaf_ slot) l ('Begin ('Leaf_ slot)) 

instance ConnectableF (old :> 'Leaf_ slot) l  a => ConnectableF (old :> 'Leaf_ slot) l  a 
--}
type Connected :: PathDir -> PathDir -> PathDir 
type family Connected p1 p2 where 
  Connected ('Begin ('Leaf_ slot)) ('Begin ('Leaf_ slot))
    =  ('Begin ('Leaf_ slot))

  Connected (old :> 'Leaf_ slot) ('Begin ('Leaf_ slot)) 
    =  (old :> 'Leaf_ slot)

  Connected old (new1 :> new2)
    = Connected old new1 :> new2 

type Connectable :: PathDir -> Trail -> PathDir -> Constraint 
class Last p2 ~ Last (Connected (old :> p1) p2) => Connectable old p1 p2 where 
  connect' :: Path root (old :> p1) -> Path slot p2 -> Path root (Connected (old :> p1) p2)

instance Connectable old ('Leaf_ slot)  ('Begin ('Leaf_ slot)) where 
           connect' (Leaf i rest) Start = Leaf i rest 

instance Connectable old p1 p2  => Connectable old p1 (p2 :> 'Leaf_ slot) where 
  connect' old = \case 
    Leaf i path -> Leaf i (connect' @old @p1 @p2 old path) 

instance (Connectable old p1 p2, Downable (Connected (old :> p1) p2) slots)  
      => Connectable old p1 (p2 :> 'Down_ slots) where 
  connect' old = \case 
    Down path -> Down (connect' @old @p1 @p2 old path)

instance (Connectable old p1 p2, Uppable (Connected (old :> p1) p2) slot) 
      => Connectable old p1 (p2 :> 'Up_ slot) where 
        connect' old = \case 
          Up path -> Up (connect' @old @p1 @p2 old path)

instance Connectable old p1 p2 => Connectable old p1 (p2 :> 'Branch_ (l ':= Slot i su cs q)) where 
  connect' old = \case 
    Branch path -> Branch $ connect' @old @p1 @p2 old path 

type ConnectHelper :: PathDir -> PathDir -> Constraint 
type family ConnectHelper p1 p2 where 
  ConnectHelper (old :> p1) p2 = Connectable old p1 p2 

class (forall slot. Connectable old ('Leaf_ slot) p2) => Connectable_ old p2 where 
  connect'' ::  forall slot root
             . (Connectable old ('Leaf_ slot) p2, Normalize (Connected (old :> 'Leaf_ slot) p2))
            => Path root (old :> 'Leaf_ slot) 
            -> Path slot p2 
            -> Path root (Connected (old :> 'Leaf_ slot) p2)
  connect'' = connect' 

instance  (forall slot. Connectable old ('Leaf_ slot) p2) => Connectable_ old p2


class  Connectable old ('Leaf_ slot) new  => CompatibleC slot old new where 
            mergePaths :: forall root 
                        . (Connectable old ('Leaf_ slot) new, Normalize (Connected (old :> 'Leaf_ slot) new))
                       => Path root (old :> 'Leaf_ slot)
                       -> Path slot new 
                       -> NormalizedPath root (NormalizeF (Connected (old :> 'Leaf_ slot)  new))
            mergePaths p1 p2 = normalize $ connect' @old  @('Leaf_ slot) @new @root p1 p2 

instance Connectable old ('Leaf_ slot) new  => CompatibleC slot old new


 
type family HasLeaf (p :: PathDir) (s :: SlotData) :: Constraint where 
  HasLeaf ('Begin ('Leaf_ slot)) slot = ()
  HasLeaf (old :> 'Leaf_ slot) slot   = ()

type family GetLeaf (p :: PathDir) :: SlotData where 
  GetLeaf ('Begin ('Leaf_ slot)) = slot 
  GetLeaf (old :> 'Leaf_ slot) = slot   

data Path :: SlotData -> PathDir -> Type where 
  Start :: forall l i q su cs. (Ord i) =>  Path (Slot i su cs q) ('Begin ('Leaf_ (Slot i su cs q)))

  Branch :: forall l i q su slots cs root old 
          . (ChildC l slots (Slot i su cs q), Ord i, Forall slots SlotOrdC) 
        => Path root (old :> 'Down_ slots) 
        -> Path root ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q))

  Leaf :: forall l q i su cs  slots old root 
        . Ord i 
       => i
       -> Path root (old :> 'Branch_ (l ':= Slot i su cs q))
       -> Path root ((old :> 'Branch_ (l ':= Slot i su cs q)) :> 'Leaf_ (Slot i su cs q))

  Down :: forall i su cs q root old s.
          Downable old cs 
       => Path root old 
       -> Path root (old :> 'Down_ cs)

  Up  :: forall  slot i su q root old1 slots 
      .  Uppable old1 slot 
      => Path root old1 
      -> Path root (old1 :> Up_ slot)

type family DownF (p :: PathDir) :: Row SlotData where 
  DownF ('Begin ('Leaf_ (Slot i su cs q)))  = cs 
  DownF (old :> 'Leaf_ (Slot i su cs q))    = cs 

class DownF p ~ cs => Downable (p :: PathDir) (cs :: Row SlotData) where 
  down :: forall l root slot. HasType l slot cs => Path root p -> Path root (p :> Down_ cs)
  down = Down 

instance Downable ('Begin ('Leaf_ (Slot i su cs q)))  cs  where 
  down Start = Down Start 

instance Downable (old :> 'Leaf_ (Slot i su cs q)) cs  where 
  down (Leaf i old) = Down (Leaf i old)

type family UpF (p :: PathDir) :: SlotData where 
  UpF ('Begin ('Leaf_ (Slot i su cs q))) = (Slot i su cs q)
  UpF (old :> 'Leaf_ (Slot i su cs q))   = Slot i su cs q 

class  UpF p ~ slot => Uppable (p :: PathDir) (slot :: SlotData) where
  up :: forall root l cs. HasType l slot cs => Path root p -> Path root (p :> Up_ slot)
  up = Up 

instance Uppable ('Begin ('Leaf_ (Slot i su cs q))) (Slot i su cs q) where 
  up Start = Up Start 

instance Uppable (old :> 'Leaf_ (Slot i su cs q)) (Slot i su cs q) where 
  up (Leaf i old) = Up (Leaf i old)

class (HasType l t rs, KnownSymbol l)=> HasType_ t rs l
instance (HasType l t rs,KnownSymbol l) => HasType_ t rs l

type HasTypeQ slot cs = DC.ForallV (HasType_ slot cs)

data NormalizedPath :: SlotData -> PathDir -> Type where 
  Start' :: forall l i q su cs. (Ord i) =>  NormalizedPath (Slot i su cs q) ('Begin ('Leaf_ (Slot i su cs q)))

  Branch' :: forall l i q su cs slots old root 
         . (KnownSymbol l, HasType l (Slot i su cs q) slots, Ord i) 
        => SlotKey l slots (Slot i su cs q) 
        -> NormalizedPath root (old :> 'Down_ slots) 
        -> NormalizedPath root ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q))

  Leaf' :: forall q i su cs l slots old root 
        . Ord i 
       => i
       -> NormalizedPath root (old :> 'Branch_ (l ':= Slot i su cs q))
       -> NormalizedPath root ((old :> 'Branch_ (l ':= Slot i su cs q)) :> 'Leaf_ (Slot i su cs q))

  Down1 :: forall i su cs q
         . NormalizedPath (Slot i su cs q) ('Begin ('Leaf_ (Slot i su cs q)))
         -> NormalizedPath (Slot i su cs q) ('Begin ('Leaf_ (Slot i su cs q)) :> 'Down_ cs)

  Down2 :: forall i su cs q root old1 
         .NormalizedPath root (old1 :> 'Leaf_ (Slot i su cs q))
       -> NormalizedPath root (old1 :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs)

