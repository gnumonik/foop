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
import Data.Bifunctor ( Bifunctor(first, bimap, second) )
import Data.Functor.Coyoneda ( Coyoneda(..), liftCoyoneda )
import Data.Proxy
import Control.Comonad.Store
import Control.Concurrent.STM.TVar
import Control.Monad.Free.Church
import Data.Row.Internal ( Extend, Row(R), LT((:->)), FrontExtends (frontExtendsDict), FrontExtendsDict (FrontExtendsDict), metamorph )
import Data.Default
import qualified Data.Row.Records as R
import Data.Constraint
import qualified Data.Constraint.Forall as DC
import Data.Type.Equality (type (:~:))
import Control.Concurrent.STM (TMVar, STM, readTMVar)
import Data.Functor.Constant
import Data.Row.Dictionaries (IsA(..),As(..),ActsOn(..),As'(..), Unconstrained1, mapExtendSwap, mapHas)
import Data.Type.Equality (type (:~:)(Refl))
import Data.Foop.Exists 
import Unsafe.Coerce
import Control.Monad.Identity
import Control.Applicative
import Data.Functor.Compose


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
  SlotKey :: (ChildC label roots slot, Forall roots (SlotI Ord), KnownSymbol label)  => SlotKey label roots slot

-- | The base functor for an entity. 
--
--   `slots` is a type of kind Row SlotData and records the data for the entity's children 
--
--   `state` is the entity's state type 
--
--   `query` is the ADT which represents the component's algebra 
--
--   `m` is the inner functor (which for now will always be IO)
type EntityF :: Row SlotData -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type
data EntityF deps roots shoots state query m a where
  State   :: (state -> (a,state)) -> EntityF deps roots shoots state query m a

  Lift    :: m a -> EntityF deps roots shoots state query m a

  Interact :: (HasType l slot deps, KnownSymbol l)
           => Label l 
          -> (ENode slot -> STM a)
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
           -> Model _loc  (Slot i su rs q)
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
        Interact l g             -> Interact l (fmap f <$> g)
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
type EntityM :: Row SlotData -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
newtype EntityM deps roots shoots state query m a = EntityM (F (EntityF deps roots shoots state query m) a) 
  deriving (Functor, Applicative, Monad)

instance Functor m => MonadState s (EntityM deps roots shoots s q m) where
  state f = EntityM . liftF . State $ f

instance  MonadIO m => MonadIO (EntityM deps roots shoots s q m) where
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM deps roots shoots s q ) where
  lift = EntityM . liftF . Lift

-- for readable partial application 
class a ~ b => Is a b where 
  is :: Dict (a ~ b)
  is = Dict 

instance a ~ b => Is a b 

-- use the fancy exists constraints if type inference doesn't work here 
data ETree :: Row SlotData -> Type where 
  ETree :: Rec (R.Map ENode slots)
        -> ETree slots 

data ENode :: SlotData -> Type where 
  ENode :: Entity (Slot i su rs q)
      --  -> ETree rs 
      --  -> EBranch ss 
        -> ENode (Slot i su rs q)

data EBranch :: Row SlotData -> Type where 
  EBranch :: Rec (R.Map ELeaf ss)
          -> EBranch ss 

data ELeaf :: SlotData -> Type where 
  ELeaf :: forall slot 
         . SlotI Ord slot 
        => M.Map (Index slot) (Entity slot)
        -> ELeaf slot

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
  = Handler {getHandler :: Store (Proxy deps) (AlgebraQ query :~> EntityM  deps roots shoots state query IO)}

class Forall ks c => All c ks where 
  allC :: Dict (Forall ks c)
  allC = Dict 
instance Forall ks c => All c ks  

data Model :: SlotData -> SlotData -> Type where 
  Model :: forall surface roots shoots query state deps i loc 
         . (SlotConstraint roots)
        => Spec loc deps shoots state (Slot i surface roots query)
        -> Model loc  (Slot i surface roots query)

data Models :: SlotData -> Row SlotData -> Type where 
  MkModels :: Rec (R.Map (Model source) models)
           -> Models source models 



 
         
-- going to have to "lift" the constraints somehow 
-- all roots and shoots have to be compatible with whatever the path 
-- to their parent entity ends up being 
-- (deferred this before but b/c need to integrate models at the spec stage, 
-- can't do so now. bleh)


-- | A `Spec` is the GADT from which an Entity is constructed. 
type Spec :: SlotData -> Row SlotData -> Row SlotData -> Type -> SlotData -> Type 
data Spec source deps shoots state slot where
  MkSpec :: forall state query (deps :: Row SlotData) surface roots shoots i source
          . ( Compat source deps
            , Forall shoots (SlotI Ord)
            , Forall roots (SlotI Ord)
            , WellBehaved shoots 
            , WellBehaved roots
            , WellBehaved (R.Map Proxy shoots)
            , SlotOrd (Slot i surface roots query)
            , Forall (R.Map Proxy shoots) Default 
            , Ord i)=>
    { initialState   :: state 
    , handleQuery    :: Handler (Slot i surface roots query) query deps roots shoots state
    , renderer       :: Renderer state surface 
    , shoots         :: Proxy shoots 
    , roots          :: Models source roots 
    , dependencies   :: Proxy (deps :: Row SlotData)
    } -> Spec source deps shoots state (Slot i surface roots query)

class All (Exists (Extends loc) (Segment 'Begin)) roots => ExtendAll loc roots 
    
type InitPath (slot :: SlotData) = ('Begin :> 'Start slot) 

initPath :: forall (slot :: SlotData) i su cs q. (slot ~ Slot i su cs q, Locate ('Begin :> 'Start slot) ) => Segment 'Begin ('Begin :> 'Start slot)
initPath = toSeg $ chart @('Begin :> 'Start slot)
-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: Row SlotData -> Row SlotData -> Row SlotData -> Type -> Type -> (Type -> Type) -> Type
data EvalState    deps roots shoots surface st q where 
  EvalState ::  {
      _entity      :: Spec loc deps shoots st (Slot i surface roots q)
    , _state       :: st
    , _shoots      :: EBranch shoots 
    , _roots       :: ETree roots
    , _surface     :: surface 
    , _environment :: Rec (R.Map STMNode deps) -- AnAtlasOf deps
    } -> EvalState  deps roots shoots surface st q 
 
-- | Existential wrapper over the EvalState record. 
data ExEvalState :: Row SlotData -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> Type where
  ExEvalState :: EvalState deps roots shoots surface st query 
              -> ExEvalState deps roots shoots surface query  

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   signficantly improve the readability of type 
data Transformer deps roots shoots surface query  where 
   Transformer :: 
     (forall x. query x -> IO (x,ExEvalState deps roots shoots surface query  )) -> Transformer deps roots shoots surface query  

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
type EntityStore ::  Row SlotData -> Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> Type 
type EntityStore deps roots shoots surface  query 
  = Store (ExEvalState deps roots shoots surface  query) (Transformer deps roots shoots surface query)

-- | `Entity surface query` is a newtype wrapper over `TVar (EntityStore surface query)`
--   Mainly for making type signatures easier.
type Entity :: SlotData -> Type 
data Entity slot where 
  Entity :: Ord i => TVar (EntityStore deps rs ss su q) -> Entity (Slot i su rs q)

-- | `Tell query` ==  `() -> query ()` 
type Tell query = () -> query ()

-- | `Request query a` == `(a -> a) -> query a` 
type Request query a = (a -> a) -> query a 

-- don't export the constructor 
type Object :: SlotData -> Type
data Object slot where 
   Object :: Entity (Slot () su rs q) -> Object (Slot () su rs q) 

---------------------------
-- Families and constraints 
---------------------------

-- | Compound constraint which a child entity must satisfy. You should probably just look at the source.
type ChildC :: Symbol -> Row SlotData -> SlotData -> Constraint
type family ChildC label slots slot where
  ChildC label slots slot 
      = ( HasType label slot slots   
        , Forall slots (SlotI Ord)
        , SlotI Ord slot 
        , KnownSymbol label)

type SlotConstraint slots = ( Forall slots (SlotI Ord)
                            , WellBehaved slots 
                            , AllUniqueLabels (R.Map Proxy slots)
                            , Forall (R.Map Proxy slots) Default)

------ *really* don't want this stuff to be here but need it in scope 

data (:=) a b = a := b deriving (Show, Eq)
infixr 8 := 

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
  Here' :: forall i su rs ss q 
         . Locate ('Begin :> 'Start (Slot i su rs q)) 
        => Segment' ('Begin :> 'Start (Slot i su rs q))

  ChildA' :: forall l l' i su rs ss q i' su' rs' ss' q' old 
         . ( KnownSymbol l'
         ,   HasType l' (Slot i' su' rs' q') rs 
   --      ,   Locate ('Begin :> Start (Slot i su rs q))
    --     ,   Locate ('Begin :> Start (Slot i su rs q) :> Down (l' ':= Slot i' su' rs' q'))
         ) => SlotKey l' rs (Slot i' su' rs' q')  
           -> Segment' ('Begin :> Start (Slot i su rs q))
           -> Segment' ('Begin :> Start (Slot i su rs q) :> Down (l' ':= Slot i' su' rs' q'))


  ChildB' :: forall l l' i su rs ss q i' su' rs' ss' q' old 
         . ( KnownSymbol l'
         ,   HasType l' (Slot i' su' rs' q') rs 
         ,   Locate (old :> 'Down (l ':= Slot i su rs q))
         ,   Locate (old :> 'Down (l ':= Slot i su rs q) :> Down (l' ':= Slot i' su' rs' q'))
         ) => SlotKey l' rs (Slot i' su' rs' q')  
           -> Segment' (old :> 'Down (l ':= Slot i su rs q))
           -> Segment' (old :> 'Down (l ':= Slot i su rs q) :> Down (l' ':= Slot i' su' rs' q'))

class Locate (path :: Path) where 
  locate :: Segment' path -> Entity (Source path) -> STM (ENode (Target path))



-- | Appends two paths 
type family Connect (parent :: Path) (child :: Path) :: Path where 
  Connect (old :> 'Down (l ':= new)) ('Begin :> 'Start new) = old :> 'Down (l ':= new)
--  Connect ('Begin :> 'Start new) ('Begin :> 'Start new) = 'Begin :> 'Start new
  Connect old (new :> Down (l ':= slot ))  = Connect old new :> Down (l ':= slot )
  Connect old (new :> Up (l ':= slot ))    = Connect old new :> Up (l ':= slot )

class Connects (parent :: Path) (child :: Path) where 
  connect :: Segment 'Begin parent -> Segment 'Begin child -> Segment 'Begin (Connect parent child)

instance Connects (old :>  Down (l ':= slot)) ('Begin ':> Start slot) where 
  connect old new = old

instance Connects old new  => Connects old (new :> Down (l ':= slot )) where 
  connect old (Child rest) = Child $ connect old rest 

instance Connects old new  => Connects old (new :> Up (l ':= slot )) where 
  connect old (Parent rest) = Parent $ connect old rest 

type family Normalize (path :: Path) :: Path where 
  -- A 
  Normalize 'Begin = 'Begin 

  -- B 
  Normalize ('Begin :> 'Start new) 
    = ('Begin :> 'Start new)

  -- C 
  Normalize ('Begin :> 'Start (Slot i' su' rs' q') :> Down (l ':= any)) 
    =  'Begin :> 'Start (Slot i' su' rs' q') :> Down (l ':= (rs' .! l))

  -- D 
  Normalize (old :> 'Down (l' ':= Slot i' su' rs' q') :> Down (l ':= any))
    =  Normalize (old :> 'Down (l' ':= Slot i' su' rs' q')) :> Down (l ':= (rs' .! l))

  -- E 
  Normalize ('Begin :> 'Start (Slot i su rs q) :> 'Down _whatever_ :> Up (l ':= Slot i su rs q)) 
    =  Normalize ('Begin :> 'Start (Slot i su rs q))

  -- F
  Normalize (old :> 'Down (l ':= Slot i su rs q) :> 'Down doesn't_Matter :> Up (l ':= Slot i su rs q)) 
    =  Normalize (old :> 'Down (l ':= Slot i su rs q))

  -- G
  Normalize (old :> 'Down (l ':= Slot i su rs q) :> Up up1 :> Up up2)  
    =  Normalize old 


type CanNormalize path = ( Source path ~ Source (Normalize path)
                         , Target path ~ Target (Normalize path)) 

class ( Target path ~ Target (Normalize path) 
      , Locate (Normalize path))=> 
  Normalizes (path :: Path) where 
        normalize :: Segment 'Begin path -> Segment' (Normalize path)

-- A/B
instance Locate ('Begin :> 'Start (Slot i su rs q)) => Normalizes ('Begin :> 'Start (Slot i su rs q)) where
  normalize Here = Here'

-- C 
instance ( KnownSymbol l' 
         , Normalizes ('Begin :> Start (Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs (SlotI Ord) 
         , Forall rs' (SlotI Ord) 
         , Locate (Normalize ('Begin :> Start (Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) )
         )
       => Normalizes ('Begin :> Start (Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
            normalize (Child old) = ChildA' SlotKey (normalize old)

-- D 
instance ( KnownSymbol l' 
         , Normalizes (old :> Down (l ':= Slot i su rs q))
         , Normalize(old :> Down (l ':= Slot i su rs q)) ~ (Normalize old :> Down (l ':= Slot i su rs q))
         , HasType l' (Slot a b c d) rs 
         , Ord a
         , Forall rs (SlotI Ord) 
         , Forall c (SlotI Ord) 
         , Locate (Normalize (old :> Down (l ':= Slot i su rs q) :> 'Down (l' ':= Slot a b c d)) )
         )
       => Normalizes (old :> Down (l ':= Slot i su rs q) :> 'Down (l' ':= Slot a b c d)) where 
            normalize (Child old) = ChildB' SlotKey $ normalize old

-- E (start down up)
instance ( Normalizes ('Begin :> 'Start (Slot i su rs q)) 
      --   , CanNormalize ('Begin :> 'Start (Slot i su rs q) :> _anything_ :> Up (l ':= Slot i su rs q))
          )
        => Normalizes ('Begin :> 'Start (Slot i su rs q) :> 'Down _anything_ :>  Up (l ':= Slot i su rs q)) where 
  normalize (Parent old) = case old of 
    Child rest -> normalize rest  

-- F (old down up)
instance ( Normalizes (old :> 'Down (l ':= Slot i su rs q)) 
      --   , CanNormalize (old :> 'Down (l ':= Slot i su rs q) :> 'Down _whatever_ :> Up (l ':= Slot i su rs q))
          )
        => Normalizes (old :> 'Down (l ':= Slot i su rs q) :> 'Down _whatever_ :>  Up (l ':= Slot i su rs q)) where 
  normalize (Parent old) = case old of 
    Child rest -> normalize rest  

-- G (old down up up)

instance (Normalizes old
        , Target old ~ Target (Normalize old)
        , Target (((old ':> 'Down (l ':= Slot i su rs q)) ':> 'Up up1) ':> 'Up up2)  ~ Target (Normalize old)
        ) => Normalizes (old :> 'Down (l ':= Slot i su rs q) :> Up up1 :> Up up2) where 
          normalize (Parent (Parent (Child old))) = normalize old 

class Normalize p ~ p => Normalized p where 
  normalized :: Dict (Normalize p ~ p)
  normalized = Dict  

instance Normalize p ~ p => Normalized p  

class Normalizes p => Charted (p :: Path) where 
  chart :: Segment' (Normalize p) 

-- A/B 
instance  Locate ('Begin :> 'Start (Slot i su rs q)) 
       => Charted ('Begin :> 'Start (Slot i su rs q)) where 
  chart = Here' 

-- C (start down)
instance ( KnownSymbol l 
         , KnownSymbol l' 
         , Charted ('Begin :> Start (Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs (SlotI Ord) 
         , Forall rs' (SlotI Ord) 
         , Locate ('Begin :> Start (Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q'))
         ) => Charted ('Begin :> Start (Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
        chart = ChildA' SlotKey Here' 

-- D (old down down)
instance ( KnownSymbol l' 
         , Charted (old :> Down (l ':= Slot i su rs q))
         , Normalizes (old :> Down (l ':= Slot i su rs q))
         , Normalize (old :> Down (l ':= Slot i su rs q)) ~ (Normalize old :> Down (l ':= Slot i su rs q))
         , HasType l' (Slot i' su' rs' q') rs 
         , Ord i'
         , Forall rs (SlotI Ord) 
         , Forall rs' (SlotI Ord) 
         , Locate  ((Normalize old ':> 'Down (l ':= Slot i su rs q))  ':> 'Down (l' ':= Slot i' su' rs' q'))
         , Locate (old :> Down (l ':= Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q'))
         )
       => Charted (old :> Down (l ':= Slot i su rs q) :> 'Down (l' ':= Slot i' su' rs' q')) where 
            chart = ChildB' SlotKey (chart @(old :> Down (l ':= Slot i su rs q)))

-- E (start down up)
instance ( Charted ('Begin :> Start (Slot i su rs q) )
         , Normalize ('Begin :> Start (Slot i su rs q)) ~ ('Begin :> Start (Slot i su rs q))
         , Normalizes ('Begin :> Start (Slot i su rs q) :> 'Down whocares :> Up (l ':= Slot i su rs q))
         )
      => Charted ('Begin :> Start (Slot i su rs q) :> 'Down whocares :> Up (l ':= Slot i su rs q)) where 
        chart = chart @('Begin :> 'Start (Slot i su rs q) )

-- F (old down up)        
instance ( Charted (old :> Down (l ':= Slot i su rs q) ))
      => Charted (old :> Down (l ':= Slot i su rs q) :> 'Down _any :> Up (l ':= Slot i su rs q)) where 
        chart = chart @(old :> Down (l ':= Slot i su rs q) )

-- G (old down up up )
instance ( Charted old 
         , Normalizes old 
         , Normalize old ~ Normalize (old :> Down _any1 :> 'Up up1 :> 'Up up2)
         , Normalizes  (old :> Down _any1 :> 'Up up1 :> 'Up up2))
      => Charted (old :> Down _any1 :> 'Up up1 :> 'Up up2) where 
        chart = chart @old

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

  sameTarget :: Target child :~: Target (Extension parent child)
  sameTarget = Refl 

  sameSource :: Source parent :~: Source (Extension parent child)
  sameSource = Refl 

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
  Source ('Begin :> 'Start a) = a 
  Source (a :> b)      = Source a 

type family Last (p :: Path) :: Step where 
  Last (a :> b) = b 

type family First (p :: Path) :: Step where 
  First ('Begin :> 'Start slot) = 'Start slot 
  First (a :> b)                = First a 

type family Target (p :: Path) :: SlotData where 
  Target (a :> 'Start b)         = b 
  Target (a :> 'Down  (l ':= b)) = b 
  Target (a :> 'Up (l ':= b))    = b 

type Slotify :: Path -> SlotData 
type family Slotify p where 
  Slotify ('Begin :> 'Start (Slot i su cs q)) = Slot i su cs q 
  Slotify (a :> b :> c) = Slotify (a :> b)

data Nat' = Z | S Nat' 

data SNat :: Nat' -> Type where 
  SZ :: SNat 'Z 
  SS :: SNat x -> SNat ('S x)

data Tagged b = Nat' :== b 

type family (<>) (xs :: [k]) (ys :: [k]) :: [k] where 
  '[] <> '[] = '[]
  '[] <> ys  = ys 
  xs  <> '[] = xs 
  (x ': xs) <>  ys = x ': (xs <> ys) 

data Index :: SlotData -> Type where 
  Ix :: forall i slot su cs q. (slot ~ Slot i su cs q, Ord i) => i -> Index slot 

instance Eq (Index (Slot i su cs q)) where 
  (Ix i) == (Ix i') = i == i' 

instance Ord (Index (Slot i su cs q)) where 
  (Ix i) <= (Ix i') = i <= i' 


{--
first we make proxies 

then we make paths to 

then we make functions 
--}

type family Project (slot :: SlotData) :: Row Path where 
  Project slot = R (ReadLabels (Projections slot))

type family ReadLabels (p :: [Path]) :: [LT Path] where 
  ReadLabels '[] = '[]
  ReadLabels (x ': xs) = ReadLabel x ': ReadLabels xs 

type family ReadLabel (p :: Path) :: LT Path where 
  ReadLabel (xs ':> Start slot) = "" ':-> (xs ':> Start slot) 
  ReadLabel (xs ':> Down (l ':= slot)) = l ':-> (xs ':> Down (l ':= slot)) 

type Projections :: SlotData -> [Path]
type family Projections slot where 
  Projections (Slot i su rs q) = ProjectionsR1 (Slot i su rs q) rs 

type ProjectionsR1 :: SlotData -> Row SlotData -> [Path] 
type family ProjectionsR1 slot slots where
  ProjectionsR1 (Slot i su rs q) (R '[]) = '[]
  ProjectionsR1 (Slot i su rs q) (R lts) = ProjectionsR2 (Slot i su rs q) lts 

type ProjectionsR2 :: SlotData -> [LT SlotData] -> [Path ]
type family ProjectionsR2 slot lts where 
  ProjectionsR2 (Slot i su rs q) '[] = '[]

  ProjectionsR2 (Slot i su rs q) (l ':-> newSlot ': rest) 
    = ('Begin :> 'Start (Slot i su rs q) :> 'Down (l ':= newSlot)) 
      ': (ConnectEmAll  ('Begin :> 'Start (Slot i su rs q) :> 'Down (l ':= newSlot)) 
                     (Projections newSlot ) 
      <> ProjectionsR2 (Slot i su rs q) rest)

type family ConnectEmAll (p :: Path) (ps :: [Path]) :: [Path] where 
  ConnectEmAll p '[] = '[] 
  ConnectEmAll p (x ': xs) = Connect p x ': ConnectEmAll p xs 

type family El (a :: k) (as :: [k]) :: Constraint where 
  El a (a ': as) = () 
  El a (x ': as) = El a as 

type El :: k -> [k] -> Constraint 
class El x xs => Elem x xs where 
  elDict :: Dict (El x xs)
  elDict = Dict 
instance El x xs => Elem x xs 

class Source path ~ slot => StartsAt slot path 
instance Source path ~ slot => StartsAt slot path  

class Each (StartsAt slot) paths => Anchored slot paths 
instance Each (StartsAt slot) paths => Anchored slot paths 

class (El p (Projections slot), Anchored slot (Projections slot)) => ProjectsTo p slot
instance (El p (Projections slot), Anchored slot (Projections slot)) => ProjectsTo p slot 

toSeg :: forall path. Segment' path -> Segment 'Begin path 
toSeg = \case 
  Here' -> Here 
  ChildA' k rest -> Child (toSeg rest)
  ChildB' k rest -> Child (toSeg rest) 
(+>) :: Segment x p1 -> (Segment x p1 -> Segment x p2) -> Segment x p2 
p1 +> p2 = p2 p1 

data SlotBox :: Type -> Type -> Row SlotData -> (Type -> Type) -> Type where 
  SlotBox :: forall i su rs q
           . SlotBox i su rs q 

data Slotted :: (Type -> Constraint) -> (Type -> Constraint) -> (Row SlotData -> Constraint) -> ((Type -> Type) -> Constraint) -> SlotData -> Type where 
  Slotted :: forall (cI :: Type -> Constraint)
                    (cS :: Type -> Constraint)
                    (cR :: Row SlotData -> Constraint)
                    (cQ :: (Type -> Type) -> Constraint)
                    (i :: Type)
                    (s :: Type)
                    (r :: Row SlotData)
                    (q :: Type -> Type)
                    (slot :: SlotData)  
           . ( slot ~ Slot i s r q
             , cI i 
             , cS s 
             , cR r 
             , cQ q
           ) => SlotBox i s r q -> Slotted cI cS cR cQ slot 

data SlotHas :: (Type -> Constraint) -> (Type -> Constraint) -> (Row SlotData -> Constraint) -> ((Type -> Type) -> Constraint) -> SlotData -> Type where 
  SlotHas :: forall (cI :: Type -> Constraint)
                    (cS :: Type -> Constraint)
                    (cR :: Row SlotData -> Constraint)
                    (cQ :: (Type -> Type) -> Constraint)
                    (i :: Type)
                    (s :: Type)
                    (r :: Row SlotData)
                    (q :: Type -> Type)
                    (slot :: SlotData)  
           . ( slot ~ Slot i s r q
             , cI i 
             , cS s 
             , cR r 
             , cQ q
           ) => SlotHas cI cS cR cQ slot 

class SlotHasC Ord Top (All SlotOrd) Top slot => SlotOrd slot 
instance SlotHasC Ord Top (All SlotOrd) Top slot => SlotOrd slot 

type SlotHasC :: (Type -> Constraint) -> (Type -> Constraint) -> (Row SlotData -> Constraint) -> ((Type -> Type) -> Constraint) -> SlotData -> Constraint 
class SlotHasC cI cS cR cQ slot where
  slotted :: Slotted cI cS cR cQ slot 

  slotHas :: SlotHas cI cS cR cQ slot 

instance (cI i, cS s, cR r, cQ q) => SlotHasC cI cS cR cQ (Slot i s r q) where 
  slotted = Slotted SlotBox 

  slotHas = SlotHas 

class SlotHasC cI Top Top Top slot => SlotI cI slot where 
  slotI :: forall i s r q. slot ~ Slot i s r q => Dict (cI i)
  slotI = case slotHas :: SlotHas cI Top Top Top slot of 
    SlotHas -> Dict  

instance SlotHasC cI Top Top Top slot => SlotI cI slot 

class SlotHasC Top cS Top Top slot => SlotS cS slot where 
  slotS :: forall i s r q. slot ~ Slot i s r q => Dict (cS s)
  slotS = case slotHas :: SlotHas Top cS Top Top slot of 
    SlotHas -> Dict  

instance SlotHasC Top cS Top Top slot => SlotS cS slot 

class SlotHasC Top Top cR Top slot => SlotR cR slot where 
  slotR :: forall i s r q. slot ~ Slot i s r q => Dict (cR r)
  slotR = case slotHas :: SlotHas Top Top cR Top slot of 
    SlotHas -> Dict  

instance SlotHasC Top Top cR Top slot => SlotR cR slot

class SlotHasC Top Top Top cQ slot => SlotQ cQ slot where 
  slotQ :: forall i s r q. slot ~ Slot i s r q => Dict (cQ q)
  slotQ = case slotHas :: SlotHas Top Top Top cQ slot of 
    SlotHas -> Dict  

instance SlotHasC Top Top Top cQ slot => SlotQ cQ slot 


newtype STMNode :: SlotData -> Type where 
  STMNode :: STM (ENode slot) -> STMNode slot    

class (Charted p, Normalized p, SourceOf p source, TargetOf p target) => ConcretePath source target p where 
  concretePath :: Dict (Charted p, Normalized p, SourceOf p source, TargetOf p target)
  concretePath = Dict 

instance (Charted p, Normalized p, SourceOf p source, TargetOf p target) => ConcretePath source target p

type family L (lt :: LT SlotData) :: Symbol where 
  L (l ':-> t) = l

type family T (lt :: LT SlotData) :: SlotData where 
  T (l ':-> t) = t
 
data HasSome' :: (k -> Constraint) -> Symbol -> Row k -> Type where 
  HasSome :: forall k (c :: k -> Constraint) (rk :: Row k) (l :: Symbol) 
          . ( WellBehaved rk 
            , KnownSymbol l 
            , HasType l (rk .! l) rk 
            , c (rk .! l)) => HasSome' c l rk 

data Some :: (k -> Constraint) -> (k -> Type) -> Type where 
  Some :: forall k (c :: k -> Constraint) (f :: k -> Type) (a :: k)
        . c a => f a -> Some c f 

unSome :: Some c f -> (forall a. c a => f a -> r) -> r 
unSome (Some a) f = f a 
   
withSome :: forall k (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) r. HasSome c l rk => (forall (x :: k). c x => r) -> r 
withSome f = case (hasSome :: HasSome' c l rk) of 
  HasSome -> f @(rk .! l)

withSome' :: forall k (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) r. HasSome' c l rk -> (forall (x :: k). c x => r) -> r 
withSome' h f = case h of 
  HasSome -> f @(rk .! l)

class HasSome (c :: k -> Constraint) (l :: Symbol) (rk :: Row k)  where 
  hasSome :: HasSome' c l rk 

instance ( HasType l (rk .! l) rk
         , c (rk .! l) 
         , WellBehaved rk 
         , KnownSymbol l ) =>  HasSome c l rk   where 
           hasSome = HasSome

class Source path ~ slot => SourceOf path slot where 
  sourceOf :: Dict (Source path ~ slot)
  sourceOf = Dict 

class Target path ~ slot => TargetOf path slot where 
  targetOf :: Dict (Target path ~ slot)
  targetOf = Dict 

instance Source path ~ slot => SourceOf path slot 

instance Target path ~ slot => TargetOf path slot 

targetOf' :: TargetOf path slot :- (Target path ~ slot)
targetOf' = Sub Dict 

getSome :: forall k (f :: k -> Type) l (c :: k -> Constraint)  (rk :: Row k) 
         . KnownSymbol l
        => HasSome' c l rk 
        -> (forall (a :: k). c a =>  f a) 
        -> Some c f 
getSome HasSome f = Some $ f @(rk .! l)

data ProxE :: forall k. k -> Type where 
  ProxE :: forall k (a :: k). Top a => ProxE a 

proxE :: forall k (a :: k). ProxE a 
proxE = ProxE  

newtype TopDict a = TopDict (Dict (Top a))

class (HasSome (ConcretePath source slot) l (Project source)
      , KnownSymbol l 
      , WellBehaved (Project source)) => Compatible source l slot where 
  unify :: TMVar (Entity source) -> STMNode slot 
  unify tmv = STMNode $ readTMVar tmv >>= \e -> 
    case hasSome :: HasSome' (ConcretePath source slot) l (Project source) of 
      h@HasSome -> case  (getSome  h proxE :: Some (ConcretePath source slot) ProxE) of 
        x -> go x e 
   where 
     go ::  Some (ConcretePath source slot) ProxE -> Entity source -> STM (ENode slot)
     go x e = unSome x (go2 e)

     go2 :: forall (a :: Path) (slot :: SlotData) (source :: SlotData)
          . ConcretePath source slot a =>  Entity source -> ProxE a -> STM (ENode slot)
     go2 e ProxE = locate @a (chart @a) e 

instance (HasSome (ConcretePath source slot) l (Project source)
      , KnownSymbol l 
      , WellBehaved (Project source)) => Compatible source l slot


class HasType l (l ':-> k) rk => HasLTK l k rk 

type ExtendLT :: Row k -> Row (LT k)
type family ExtendLT rk = lt | lt -> rk  where 
  ExtendLT (R lts) = R (ExtendLTR lts) 

type ExtendLTR :: [LT k] -> [LT (LT k)]
type family ExtendLTR rk = lt | lt -> rk  where 
  ExtendLTR '[] = '[]
  ExtendLTR (l ':-> k ': lts) = (l ':-> (l ':-> k)) ': ExtendLTR lts 

type RetractLT :: Row (LT k) -> Row k 
type family RetractLT lt = rk | rk -> lt where 
  RetractLT (R lts) = R (RetractLTR lts)

type RetractLTR :: [LT (LT k)] -> [LT k] 
type family RetractLTR lt = rk | rk -> lt where 
  RetractLTR '[] = '[]
  RetractLTR (l ':-> (l ':-> k) ': lts) = l ':-> k ': RetractLTR lts 

class ExtendLT rk ~ lt => ExtendsLT rk lt | lt -> rk where 
  extendLT :: Dict (ExtendLT rk ~ lt) 
  extendLT = Dict 

instance ExtendLT rk ~ lt => ExtendsLT rk lt 

class RetractLT lt ~ rk => RetractsLT lt rk | rk -> lt where 
  retractLT :: Dict (RetractLT lt ~ rk)
  retractLT = Dict 

instance RetractLT lt ~ rk => RetractsLT lt rk 

class ( ExtendsLT (rk :: Row k) (lt :: Row (LT k))
      , RetractsLT lt rk) => 
    LTSOf (rk :: Row k) (lt :: Row (LT k)) where 
  ltsOf :: forall (l :: Symbol) (t :: k) 
         .  HasType l t rk :- HasType l (l ':-> t) lt 
  ltsOf = Sub (unsafeCoerce (Dict :: Dict (HasType l t rk))) 


instance (ExtendsLT (rk :: Row k) (lt :: Row (LT k)), RetractsLT lt rk) => LTSOf (rk :: Row k) (lt :: Row (LT k))

mkProxy :: forall slots. ( AllUniqueLabels slots
         , AllUniqueLabels (R.Map Proxy slots)
         , Forall (R.Map Proxy slots) Default
         ) => Proxy slots 
           -> Rec (R.Map Proxy slots)
mkProxy Proxy = R.default' @Default def



hasType :: forall l t r. HasType l t r :- ((r .! l) ~ t) 
hasType  = Sub Dict 



-- | This is the same as @(lazyRemove l r, r .! l)@.
lazyUncons :: KnownSymbol l => Label l -> Rec r -> (Rec (r .- l), r .! l)
lazyUncons l r = (R.lazyRemove l r, r .! l)



class HasType l t r => HasTypeAt r t l where 
  hasType' :: Dict (HasType l t r)
  hasType' = Dict 

instance HasType l t r => HasTypeAt r t l   


class ForallL (r :: Row k) (c :: Symbol -> k -> Constraint) -- (c' :: Symbol -> Constraint) 
  where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  -- The parameter 'p' describes the output of the unfold and the input of the fold.
  -- For records, @p = (,)@, because every entry in the row will unfold to a value paired
  -- with the rest of the record.
  -- For variants, @p = Either@, because there will either be a value or future types to
  -- explore.
  -- 'Const' can be useful when the types in the row are unnecessary.
  metamorphL :: forall (p :: Type -> Type -> Type) (f :: Row k -> Type) (g :: Row k -> Type) (h :: k -> Type). Bifunctor p
            => Proxy (Proxy h, Proxy p)
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
               => Label ℓ -> f ρ -> p (f (ρ .- ℓ)) (h τ))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
               => Label ℓ -> p (g ρ) (h τ) -> g (Extend ℓ τ ρ))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r

instance ForallL (R '[]) c  where
  {-# INLINE metamorphL #-}
  metamorphL _ empty _ _ = empty

instance (KnownSymbol ℓ, c ℓ τ, ForallL ('R ρ) c, FrontExtends ℓ τ ('R ρ), AllUniqueLabels (Extend ℓ τ ('R ρ))) => ForallL ('R (ℓ :-> τ ': ρ) :: Row k) c where
  {-# INLINE metamorphL #-}
  metamorphL h empty uncons cons = case frontExtendsDict @ℓ @τ @('R ρ) of
    FrontExtendsDict Dict ->
      cons (Label @ℓ) . first (metamorphL @_ @('R ρ) @c h empty uncons cons) . uncons (Label @ℓ)


newtype RMap (f :: Type -> Type) (ρ :: Row Type) = RMap { unRMap :: Rec (R.Map f ρ) }
newtype RMap2 (f :: Type -> Type) (g :: Type -> Type) (ρ :: Row Type) = RMap2 { unRMap2 :: Rec (R.Map f (R.Map g ρ)) }

newtype RMapK  (f :: k -> Type) (ρ :: Row k) = RMapK { unRMapK :: Rec (R.Map f ρ) }
newtype RMap2K (f :: Type -> Type) (g :: k -> Type) (ρ :: Row k) = RMap2K { unRMap2K :: Rec (R.Map f (R.Map g ρ)) }

class ( ForallL deps (Compatible source)
      , Forall (R.Map Proxy deps) Default
      , WellBehaved deps 
      , WellBehaved (R.Map Proxy deps)
      ) => Compat source deps where 
  compat :: TMVar (Entity source) -> Rec (R.Map STMNode deps) 
  compat tmv = transformWithLabels @SlotData @(Compatible source) @deps @Proxy @STMNode go (mkProxy (Proxy @deps)) 
    where 
      go :: forall (l :: Symbol) (s :: SlotData)
          . (KnownSymbol l)
         => Dict (Compatible source l s) 
         -> Proxy s 
         -> STMNode s 
      go Dict Proxy = unify @source @l @s tmv  

instance ( ForallL deps (Compatible source)
      , Forall (R.Map Proxy deps) Default
      , WellBehaved deps 
      , WellBehaved (R.Map Proxy deps)
      ) => Compat source deps 

-- | A function to map over a record given a constraint.
mapWithLabels :: forall c f r. ForallL r c => (forall l a. (KnownSymbol l, c l a) => a -> f a) -> Rec r -> Rec (R.Map f r)
mapWithLabels f = unRMap . metamorphL @_ @r @c @(,) @Rec @(RMap f) @f Proxy doNil doUncons doCons
  where
    doNil _ = RMap R.empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
             => Label ℓ -> Rec ρ -> (Rec (ρ .- ℓ), f τ)
    doUncons l = second (f @ℓ). lazyUncons l
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ)
           => Label ℓ -> (RMap f ρ, f τ) -> RMap f (Extend ℓ τ ρ)
    doCons l (RMap r, v) = RMap (R.extend l v r)
      \\ mapExtendSwap @f @ℓ @τ @ρ

transformWithLabels :: forall k c r (f :: k -> Type) (g :: k -> Type)
                     . ForallL r c
                    => (forall l a. (KnownSymbol l) => Dict (c l a) -> f a -> g a) 
                    -> Rec (R.Map f r) 
                    -> Rec (R.Map g r)
transformWithLabels f = unRMapK . metamorphL @_ @r @c @(,) @(RMapK f) @(RMapK g) @f Proxy doNil doUncons doCons . RMapK
  where
    doNil _ = RMapK R.empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
             => Label ℓ -> RMapK f ρ -> (RMapK f (ρ .- ℓ), f τ)
    doUncons l (RMapK r) = first RMapK $ lazyUncons l r
      \\ mapHas @f @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ)
           => Label ℓ -> (RMapK g ρ, f τ) -> RMapK g (Extend ℓ τ ρ)
    doCons l (RMapK r, v) = RMapK (R.extend l (f (Dict :: Dict (c ℓ τ)) v) r)
      \\ mapExtendSwap @g @ℓ @τ @ρ


