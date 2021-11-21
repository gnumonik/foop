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
import Data.Type.Equality (type (:~:))
import Control.Concurrent.STM (TMVar, STM)
import Data.Functor.Constant
import Data.Row.Dictionaries (IsA(..),As(..),ActsOn(..),As'(..), Unconstrained1)
import Data.Type.Equality (type (:~:)(Refl))
import Data.Foop.Exists 

--- *** Finish fixing paths so start doesn't have a label (this gives us an isomorphism between paths and well-formed slotdata)
--- *** Write the isomorphism function(s)
--- roots and shoots can both have upward constraints but they only need to be satisfied 
--- during spec creation for roots. the hard part is going to be finding a way to percolate those constraints upwards...
--- easiest way would just be to union the deps of all roots (extended with their parent) onto the deps of the parent
--- let's try that 
{-- 

Important observation!!
  Every part of the path to an entity's current location must exist if the entity does 


in spirit: 

ETree = ENode (Entity (Slot i su (R.Map ETree rs) (R.Map Ebranch ss) q))

so the main difference is that root contains nodes whereas shoot contains branches 

--}

------------
-- Types 
------------

-- | This is a kind; it only exists at the typelevel and its only purpose is 
-- to function as inputs to the type families which construct the render tree 
-- and the child entity storage 
type SlotData = (Type,Type,Type,Type -> Type)

-- | Slot index surface query
--   
--   Typelevel tuples realllllyyyyy suck syntactically so this 
--   synonym allows our users to avoid typing them out in type applications 
--   Source argument will have to satisfy an Ord constraint but there's no way 
--   to express that here. 
type Slot :: Type -> Type -> Row SlotData ->  (Type -> Type) ->  SlotData 
type Slot index surface roots  query = '(index,surface,ETree roots,query)



-- | GADT which records the necessary Slot Data and functions as a kind of 
--   key for operations over child entities. It shouldn't ever be necessary for 
--   a user to manually construct this
data SlotKey :: Symbol -> Row SlotData -> SlotData -> Type where
  SlotKey :: (ChildC label roots slot, Forall roots SlotOrdC)  => SlotKey label roots slot

-- | The base functor for an entity. 
--
--   `slots` is a type of kind Row SlotData and records the data for the entity's children 
--
--   `state` is the entity's state type 
--
--   `query` is the ADT which represents the component's algebra 
--
--   `m` is the inner functor (which for now will always be IO)
type EntityF :: Row Type -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type
data EntityF deps roots shoots state query m a where
  State   :: (state -> (a,state)) -> EntityF deps roots shoots state query m a

  Lift    :: m a -> EntityF deps roots shoots state query m a

  Interact :: (HasType l (Segment 'Begin path) deps, KnownSymbol l)
          => Label l 
          -> (Entity (Target path) -> a)
          -> EntityF deps roots shoots state query m a 

  Query    :: Coyoneda query a -> EntityF deps roots shoots state query m a

  GetShoot :: SlotKey l shoots slot 
           -> (ELeaf slot -> a) 
           -> EntityF deps roots shoots state query m a

  GetRoot :: SlotKey l roots slot 
          -> (ENode slot -> a)
          -> EntityF deps roots shoots state query m a

  Create   :: SlotKey l shoots (Slot i su rs q)
           -> Label l 
           -> i
           -> Model ds (Slot i su rs q)
           -> a 
           -> EntityF deps roots shoots state query m a

  Delete   :: SlotKey l slots (Slot i su rs q)
           -> i
           -> a 
           -> EntityF deps roots shoots state query m a

instance Functor m => Functor (EntityF deps roots shoots state query m) where
  fmap f =  \case
        State k                  -> State (first f . k)
        Lift ma                  -> Lift (f <$> ma)
        Interact path g          -> Interact path (fmap f g) 
        Query qb                 -> Query $ fmap f qb
        GetShoot key g           -> GetShoot key $ fmap f g -- (goChild f key g)
        GetRoot key g            -> GetRoot key (fmap f g)
        Create s@SlotKey l i e a -> Create s l i e (f a)
        Delete key i a           -> Delete key i (f a)

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
type EntityM :: Row Type -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
newtype EntityM deps roots shoots state query m a = EntityM (F (EntityF deps roots shoots state query m) a) 
  deriving (Functor, Applicative, Monad)

instance Functor m => MonadState s (EntityM deps roots shoots s q m) where
  state f = EntityM . liftF . State $ f

instance  MonadIO m => MonadIO (EntityM deps roots shoots s q m) where
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM deps roots shoots s q ) where
  lift = EntityM . liftF . Lift

data Model :: Row Type  -> SlotData -> Type where 
  Model :: forall surface roots shoots query state deps i
         . (SlotConstraint roots)
        => Spec deps shoots state (Slot i surface roots query)
        -> Model deps (Slot i surface roots query)

-- use the fancy exists constraints if type inference doesn't work here 
data ETree :: Row SlotData -> Type where 
  ETree :: Rec (R.Map ENode slots)
        -> ETree slots 

data ENode :: SlotData -> Type where 
  ENode :: Entity (Slot i su rs q)
        -> ETree rs 
        -> EBranch ss 
        -> ENode (Slot i su rs q)

data EBranch :: Row SlotData -> Type where 
  EBranch :: Rec (R.Map ELeaf ss)
          -> EBranch ss 

data ELeaf :: SlotData -> Type where 
  Eleaf :: M.Map (Indexed (Slot i su rs q)) (Entity (Slot i su rs q))
        -> ELeaf (Slot i su rs q)

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

newtype Handler slot query deps roots shoots state 
  = Handler {getHandler :: Store (MkPaths slot deps) (AlgebraQ query :~> EntityM  deps roots shoots state query IO)}

class Forall ks c => All c ks where 
  allC :: Dict (Forall ks c)
  allC = Dict 
instance Forall ks c => All c ks  

-- lol @ this
type AllCompatibleModels parent models 
  = Forall models (Exists2 (All (Exists (Extends parent) (Segment 'Begin))) Unconstrained1 Model)

data Shoots :: Row SlotData -> Type where 
  MkShoots :: forall shoots 
            .  Shoots shoots 

data Roots :: Path -> Row Type -> Type where 
  MkRoots :: forall parent roots 
           . AllCompatibleModels parent roots 
          => Rec roots 
          -> Roots parent roots 
         
-- going to have to "lift" the constraints somehow 
-- all roots and shoots have to be compatible with whatever the path 
-- to their parent entity ends up being 
-- (deferred this before but b/c need to integrate models at the spec stage, 
-- can't do so now. bleh)

-- | A `Spec` is the GADT from which an Entity is constructed. 
type Spec ::  Row Type -> Row SlotData -> Type -> SlotData -> Type 
data Spec deps shoots state slot where
  MkSpec :: forall state query deps surface roots shoots i.
   ( WellBehaved roots) => 
    { initialState   :: state 
    , handleQuery    :: Handler (Slot i surface roots query) query deps roots shoots state  -- AlgebraQ query :~> EntityM deps slots state query IO 
    , renderer       :: Renderer state surface 
    , slots          :: Proxy roots 
    } -> Spec deps shoots state (Slot i surface roots query)

-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: Row Type -> Row SlotData -> Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState   deps roots shoots surface st q where 
  EvalState :: (SlotConstraint roots) => {
      _entity      :: Spec deps shoots st (Slot i surface roots q)
    , _state       :: st
    , _shoots      :: EBranch shoots 
    , _roots       :: ETree roots
    , _surface     :: surface 
    -- , _environment :: AnAtlasOf deps
    } -> EvalState  deps roots shoots surface st q 

-- | Existential wrapper over the EvalState record. 
data ExEvalState :: Row Type -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> Type where
  ExEvalState :: ( SlotConstraint slots) 
              => EvalState deps roots shoots surface st query 
              -> ExEvalState deps roots shoots surface query  

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   signficantly improve the readability of type 
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
type EntityStore ::  Row Type -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> Type 
type EntityStore deps roots shoots surface  query 
  = Store (ExEvalState deps roots shoots surface  query) (Transformer deps roots shoots surface query)

-- | `Entity surface query` is a newtype wrapper over `TVar (EntityStore surface query)`
--   Mainly for making type signatures easier.
type Entity :: SlotData -> Type 
data Entity slot where 
  Entity :: (SlotOrdC (Slot i su rs q)) 
         => TVar (EntityStore deps rs ss su q) -> Entity (Slot i su rs q)

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
   Object :: Entity (Slot () su rs q) -> Object (Slot () su rs q) 

---------------------------
-- Families and constraints 
---------------------------

type IndexOf :: SlotData -> Type
type family IndexOf slotData where 
  IndexOf (Slot i s rs q) = i

unIndexed :: Indexed '(i,su,rs,q)
          -> i 
unIndexed (Indexed Index i) = i 

data Index :: SlotData -> Type -> Type where 
  Index :: Ord i => Index (Slot i su rs q) i 

instance Show i => Show (Indexed (Slot i su rs q)) where 
  show (Indexed Index i) = show i 

data Indexed :: SlotData ->  Type where 
  Indexed :: Index slot i -> i -> Indexed slot  

instance Eq (Indexed slot) where 
  (Indexed Index i) == (Indexed Index i') = i == i' 

instance Ord (Indexed slot ) where 
  (Indexed Index i) <= (Indexed Index i') = i <= i' 

type Index' :: SlotData -> Type 
type family Index' slotData where 
  Index' (Slot i su rs q) = Index (Slot i su rs q) i

newtype StorageBox :: SlotData -> Type where 
  MkStorageBox :: M.Map (Indexed slot) (Entity slot) 
               -> StorageBox slot

-- | Constructs a storage record from a row of slotdata.
type MkStorage :: Row SlotData -> Row Type
type family MkStorage slotData  where
  MkStorage slotData = R.Map StorageBox slotData 

type family SlotC (slot :: SlotData) :: Constraint where 
  SlotC '(i,s,ETree cs,q) = (Ord i, Forall cs SlotOrdC)

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

type SlotConstraint slots = ( Forall slots SlotOrdC 
                            , WellBehaved slots 
                            , AllUniqueLabels (R.Map Proxy slots)
                            , Forall (R.Map Proxy slots) Default)

------ *really* don't want this stuff to be here but need it in scope 

data (:=) a b = a := b deriving (Show, Eq)
infixr 8 := 

data MkPaths ::  SlotData -> Row Type -> Type where 
  MkPaths :: forall  slot paths 
           .  -- AllRooted slot paths => 
              Rec paths 
           -> MkPaths slot paths  

  NoDeps :: forall slot. MkPaths slot Empty  

data Dir a b
  = Up (a := b) 
  | Down (a := b) 
  | Start b

type Step = Dir Symbol SlotData

type Path = Crumbs Step

data Segment :: Path -> Path -> Type where 
  Here   :: forall l start (slot :: SlotData)
         . Segment start (start :> Start slot)

  Parent :: forall start old new    
        . Segment start old 
       -> Segment start (old :> Up new)

  Child :: forall start old new    
        . Segment start old 
       -> Segment start (old :> Down new)

data Segment' :: Path -> Type where 
  Here' :: forall l i su rs ss q 
        . KnownSymbol l 
       => Segment' ('Begin :> 'Start (Slot i su rs q))

  Child' :: forall l l' i su rs ss q i' su' rs' ss' q' old k (f :: (Symbol := SlotData) -> Dir (Symbol := SlotData))
         . ( KnownSymbol l'
         ,   HasType l' (Slot i' su' rs' q') rs 
         ) => SlotKey l' rs (Slot i' su' rs' q')  
           -> Segment' (old :> f (l ':= Slot i su rs q))
           -> Segment' (old :> f (l ':= Slot i su rs q) :> Down (l' ':= Slot i' su' rs' q'))

class Locate (path :: Path) where 
  locate :: Segment' path -> Entity (Source path) -> STM (ENode (Target path))

-- | Appends two paths 
type family Connect (parent :: Path) (child :: Path) :: Path where 
  Connect old ('Begin :> 'Start new) = old :> 'Down new  
  Connect old (new :> Down (l ':= slot ))  = Connect old new :> Down (l ':= slot )
  Connect old (new :> Up (l ':= slot ))    = Connect old new :> Up (l ':= slot )

class Connects (parent :: Path) (child :: Path) where 
  connect :: Segment 'Begin parent -> Segment 'Begin child -> Segment 'Begin (Connect parent child)

instance Connects (old :> new :> Down (l ':= slot)) ('Begin ':> Start x) where 
  connect old Here = Child old 

instance Connects old new  => Connects old (new :> Down (l ':= slot )) where 
  connect old (Child rest) = Child $ connect old rest 

instance Connects old new  => Connects old (new :> Up (l ':= slot )) where 
  connect old (Parent rest) = Parent $ connect old rest 

type family Normalize (path :: Path) :: Path where 
  Normalize 'Begin = 'Begin 

  Normalize ('Begin :> 'Start new) 
    = ('Begin :> 'Start new)

  Normalize (old :> Down (l ':= Slot i su rs q)) 
    =  Normalize old :> Down (l ':= Slot i su rs q)

  Normalize (old :> f (l ':= Slot i su rs q) :> doesn't_Matter :> Up (l ':= Slot i su rs q)) 
    =  Normalize (old :> f (l ':= Slot i su rs q))

type CanNormalize path = ( Source path ~ Source (Normalize path)
                         , Target path ~ Target (Normalize path)) 

class CanNormalize path => Normalizes (path :: Path) where 
        normalize :: Segment 'Begin path -> Segment' (Normalize path)

instance KnownSymbol l => Normalizes ('Begin :> 'Start (Slot i su rs q)) where
  normalize Here = Here'

instance ( Normalizes (old :> f (l ':= Slot i su rs q)) 
         , CanNormalize (old :> f (l ':= Slot i su rs q) :> _anything_ :> Up (l ':= Slot i su rs q)) 
         , Normalize (old ':> f (l ':= Slot i su rs q)) ~ (Normalize old ':> f (l ':= Slot i su rs q)))
        => Normalizes (old :> f (l ':= Slot i su rs q) :> _anything_ :>  Up (l ':= Slot i su rs q)) where 
  normalize (Parent old) = case old of 
    Parent rest -> normalize rest 
    Child rest -> normalize rest  


instance ( KnownSymbol l' 
         , Normalizes (old :> Down (l ':= Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs SlotOrdC 
         , Forall rs' SlotOrdC 
         )
       => Normalizes (old :> Down (l ':= Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
            normalize (Child old) = Child' SlotKey (normalize old)

instance ( KnownSymbol l' 
         , Normalizes ('Begin :> Start (Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs SlotOrdC 
         , Forall rs' SlotOrdC 
         )
       => Normalizes ('Begin :> Start (l ':= Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
            normalize (Child old) = Child' SlotKey (normalize old)

class Normalizes p => Charted (p :: Path) where 
  chart :: Segment' (Normalize p) 

instance KnownSymbol l => Charted ('Begin :> 'Start (l ':= Slot i su rs q)) where 
  chart = Here'

instance ( Charted (old :> Down (l ':= Slot i su rs q) ))
      => Charted (old :> Down (l ':= Slot i su rs q) :> whocares :> Up (l ':= Slot i su rs q)) where 
        chart = chart @(old :> Down (l ':= Slot i su rs q) )

instance ( Charted ('Begin :> Start (l ':= Slot i su rs q) )
         , Normalize ('Begin :> Start (l ':= Slot i su rs q)) ~ ('Begin :> Start (l ':= Slot i su rs q))
         )
      => Charted ('Begin :> Start (l ':= Slot i su rs q) :> whocares :> Up (l ':= Slot i su rs q)) where 
        chart = chart @('Begin :> 'Start (l ':= Slot i su rs q) )

instance ( KnownSymbol l 
         , KnownSymbol l' 
         , Charted ('Begin :> Start (l ':= Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs SlotOrdC 
         , Forall rs' SlotOrdC 
         ) => Charted ('Begin :> Start (l ':= Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
        chart = Child' SlotKey Here' 

instance ( KnownSymbol l' 
         , Charted (old :> Down (l ':= Slot i su rs q))
         , Normalizes (old :> Down (l ':= Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs SlotOrdC 
         , Forall rs' SlotOrdC 
         )
       => Charted (old :> Down (l ':= Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
            chart = Child' SlotKey (chart @(old :> Down (l ':= Slot i su rs q)))

type Extension parent child = Normalize (Connect parent child)

class ( Connects parent child
      , Normalizes (Connect parent child)
      , Charted (Extension parent child)
      , Locate (Extension parent child)
      , Target child ~ Target (Extension parent child)
      , Source parent ~ Source (Extension parent child)) 
   => Extends parent child where 
  extendPath :: Segment 'Begin parent 
             -> Segment 'Begin child 
             -> Segment' (Extension parent child)
  extendPath p c = normalize $ connect p c 

instance ( Connects parent child
      , Normalizes (Connect parent child)
      , Locate (Extension parent child)
      , Charted (Extension parent child)
      , Target child ~ Target (Extension parent child)
      , Source parent ~ Source (Extension parent child)) 
   => Extends parent child 

data AnAtlasOf :: Row Type -> Type where 
  AnAtlasOf :: Forall children (Exists (Extends parent) (Segment 'Begin)) 
            => Atlas parent children 
            -> AnAtlasOf children 

data Atlas :: Path -> Row Type -> Type where 
  MkAtlas :: forall parent children 
           . TMVar (Entity (Source parent))
          -> Unified parent children 
          -> Atlas parent children

data Navigator :: Path -> Path -> Type where 
  MkNavigator :: forall source destination 
              . (Entity (Source source) -> STM (ENode (Target destination)))
              -> Navigator source destination

type Unified parent children 
  = Rec (R.Map (Deriving (Extends parent) (Segment 'Begin) (Navigator parent)) children)

data Crumbs a = Begin | Crumbs a :> a
infixl 1 :>
deriving instance Show a => Show (Crumbs a) 

type family Source (p :: Path) :: SlotData where 
  Source ('Begin :> 'Start (l ':= a)) = a 
  Source (a :> b)      = Source a 

type family Last (p :: Path) :: Step where 
  Last (a :> b) = b 

type family First (p :: Path) :: Step where 
  First ('Begin :> 'Start slot) = 'Start slot 
  First (a :> b) = First a 

type family Target (p :: Path) :: SlotData where 
  Target (a :> 'Start (l ':= b)) = b 
  Target (a :> 'Down  (l ':= b)) = b 
  Target (a :> 'Up (l ':= b))    = b 


-- 


