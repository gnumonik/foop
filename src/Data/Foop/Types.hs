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
  SlotKey :: ChildC label slots slot  => SlotKey label slots slot

-- | The base functor for an entity. 
--
--   `slots` is a type of kind Row SlotData and records the data for the entity's children 
--
--   `state` is the entity's state type 
--
--   `query` is the ADT which represents the component's algebra 
--
--   `m` is the inner functor (which for now will always be IO)
type EntityF :: Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type
data EntityF slots  state query m a where
  State   :: (state -> (a,state)) -> EntityF slots  state query m a

  Lift    :: m a -> EntityF slots state query m a

  Query   :: Coyoneda query a -> EntityF slots state query m a

  Child   :: SlotKey l slots slot 
          -> (StorageBox slot -> a) 
          -> EntityF slots state query m a

  Create  :: SlotKey l slots '(i,su,RenderTree cs,q)
          -> i
          -> Prototype su cs q 
          -> a 
          -> EntityF slots state query m a

  Delete :: SlotKey l slots '(i,su,RenderTree cs,q)
         -> i
         -> a 
         -> EntityF slots state query m a



instance Functor m => Functor (EntityF slots state query m) where
  fmap f = \case
    State k          -> State (first f . k)
    Lift ma          -> Lift (f <$> ma)
    Query qb         -> Query $ fmap f qb
    Child key g      -> Child key $ fmap f g-- (goChild f key g)
   -- Surface key g    -> Surface key $ fmap f g
    Create key i e a -> Create key i e (f a)
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
newtype EntityM slots state query m a = EntityM (F (EntityF slots state query m) a) 
  deriving (Functor, Applicative, Monad)

instance Functor m => MonadState s (EntityM slots s q m) where
  state f = EntityM . liftF . State $ f

instance  MonadIO m => MonadIO (EntityM slots s q m) where
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM slots s q ) where
  lift = EntityM . liftF . Lift


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

instance (Show surface, Show (RenderTree children)) => Show (RenderLeaf (Slot i surface children q)) where 
  show (MkRenderLeaf su cs) = "MkRenderLeaf " <> show su <> show cs 
  
-- | `Prototype` is an existential wrapper for `Spec` which hides 
--   the spec's state and slot types. Only the surface (i.e. the type which the state renders to)
--   and the query algebra are exposed.
data Prototype :: Type -> Row SlotData -> (Type -> Type) -> Type where
  Prototype :: SlotConstraint slots 
            => Spec slots surface  state query
            -> Prototype surface slots query

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

-- | A `Spec` is the GADT from which an Entity is constructed. 
type Spec :: Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data Spec slots surface state query  where
  MkSpec ::
   (--Forall slots SlotDataC,
    WellBehaved slots) => 
    { initialState   :: state -- For existential-ey reasons this has to be a function
    , handleQuery    :: AlgebraQ query :~> EntityM slots state query IO
    , renderer       :: Renderer state surface 
    , slots          :: Proxy slots
    } -> Spec slots surface state query

-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState slots surface  st q where 
  EvalState :: {
      _entity     :: Spec slots surface st q
    , _state      :: st
    , _storage    :: Rec (MkStorage slots)
    , _surface    :: surface 
  } -> EvalState slots surface st q 

-- | Existential wrapper over the EvalState record. 
data ExEvalState :: Type -> Row SlotData -> (Type -> Type) -> Type where
  ExEvalState :: EvalState slots surface st q
              -> ExEvalState surface slots  q

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   make type signatures far more readable. 
newtype Transformer surface slots query = Transformer {transform :: forall x. query x -> IO (x,ExEvalState surface slots query)}

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
type EntityStore :: Type -> Row SlotData -> (Type -> Type) -> Type 
type EntityStore surface children query = Store (ExEvalState surface children query) (Transformer surface children query)

-- | `Entity surface query` is a newtype wrapper over `TVar (EntityStore surface query)`
--  
--   Mainly for making type signatures easier.
type Entity :: SlotData -> Type 
data Entity slot where 
  Entity :: SlotOrdC '(i,su,RenderTree cs,q) 
         => TVar (EntityStore su cs q) -> Entity '(i,su,RenderTree cs,q)

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

-- we have to "existentially hide" (that's not really what's going on)
class QueryOf_ slot  ~ q => QueryOf (slot :: SlotData) (q :: Type -> Type)
instance QueryOf_ slot ~ q => QueryOf slot q 

type SurfaceOf_ :: SlotData -> Type 
type family SurfaceOf_ slot where 
  SurfaceOf_ '(i,su,cs,q) = su 

class SurfaceOf_ slot ~ su    => SurfaceOf slot su 
instance SurfaceOf_ slot ~ su => SurfaceOf slot su 

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


