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
import Data.Foop.RowExtras
import Data.Constraint.Deferrable 
import Data.Singletons (KindOf, Sing, SingI (sing))
import Data.Singletons.TypeLits (withKnownSymbol)




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
type Slot :: Type -> Row SlotData -> Row SlotData ->  (Type -> Type) ->  SlotData 
type Slot surface roots deps  query = '(surface,ETree roots, Deps deps,query)

type IxSlotData = (Type,SlotData)

type IxSlot :: Type -> SlotData -> IxSlotData 
type IxSlot t s = '(t,s)
 

data Deps :: Row SlotData -> Type where 
  MkDeps :: Forall deps Unconstrained1 => Proxy deps -> Deps deps 

-- | GADT which records the necessary Slot Data and functions as a kind of 
--   key for operations over child entities. It shouldn't ever be necessary for 
--   a user to manually construct this
data SlotKey :: Symbol -> Row SlotData -> SlotData -> Type where
  SlotKey :: (HasType label slot roots, KnownSymbol label)  => SlotKey label roots slot

data ShootKey :: Symbol -> Row IxSlotData -> IxSlotData -> Type where
  ShootKey :: (HasType label (IxSlot i slot) shoots, KnownSymbol label)  
           => ShootKey label shoots (IxSlot i slot)

-- | The base functor for an entity. 
--
--   `slots` is a type of kind Row SlotData and records the data for the entity's children 
--
--   `state` is the entity's state type 
--
--   `query` is the ADT which represents the component's algebra 
--
--   `m` is the inner functor (which for now will always be IO)
type EntityF :: Row SlotData -> Row SlotData -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type
data EntityF deps roots surface state query m a where
  State   :: (state -> (a,state)) -> EntityF deps roots surface state query m a

  Lift    :: m a -> EntityF deps roots surface state query m a

  Interact :: (HasType l slot deps, KnownSymbol l)
           => Label l 
          -> (ENode slot -> STM a)
          -> EntityF deps roots surface state query m a 

  Origin   :: (Origin (Slot surface roots deps query) -> a) 
           -> EntityF deps roots surface state query m a 

  Query    :: Coyoneda query a -> EntityF deps roots surface state query m a
{-
  GetShoot :: ShootKey l shoots slot 
           -> (ELeaf slot -> a) 
           -> EntityF deps roots shoots state query m a
-}
  GetRoot :: SlotKey l roots slot 
          -> (ENode slot -> a)
          -> EntityF deps roots surface state query m a
{-
  Create   :: ShootKey l shoots (IxSlot i (Slot su rs ds q))
           -> Label l 
           -> i
           -> Model  (Slot su rs ds q)
           -> a 
           -> EntityF deps roots shoots state query m a

  Delete   :: ShootKey l (IxSlot i (Slot su rs ds q))
           -> i
           -> a 
           -> EntityF deps roots state query m a
-}
instance Functor m => Functor (EntityF deps roots surface state query m) where
  fmap f =  \case
        State k                  -> State (first f . k)
        Lift ma                  -> Lift (f <$> ma)
        Origin g                 -> Origin (f <$> g)
        Interact l g             -> Interact l (fmap f <$> g)
        Query qb                 -> Query $ fmap f qb
        GetRoot key g            -> GetRoot key (fmap f g)

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
type EntityM :: Row SlotData -> Row SlotData -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
newtype EntityM deps roots surface state query m a = EntityM (F (EntityF deps roots surface state query m) a) 
  deriving (Functor, Applicative, Monad)

instance Functor m => MonadState st (EntityM deps roots su st q m) where
  state f = EntityM . liftF . State $ f

instance  MonadIO m => MonadIO (EntityM deps roots su st q m) where
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM deps roots su st q ) where
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
  ENode :: Entity (Slot su rs ds q)
      --  -> ETree rs 
      --  -> EBranch ss 
        -> ENode (Slot su rs ds q)

data EBranch :: Row IxSlotData -> Type where 
  EBranch :: Rec (R.Map ELeaf ss)
          -> EBranch ss 

data ELeaf :: IxSlotData -> Type where 
  ELeaf :: forall i slot 
         . Ord i 
        => M.Map i (Entity slot)
        -> ELeaf (IxSlot i slot)

data MkSlotI :: IxSlotData ->  Type where 
  MkSlotI :: forall (i :: Type) (slot :: SlotData)
           . Ord i => MkSlotI (IxSlot i slot)

class SlotOrd (iSlot :: IxSlotData) where 
  slotOrd :: MkSlotI iSlot 

  emptyLeaf :: ELeaf iSlot 

instance Ord i => SlotOrd (IxSlot i slot) where 
  slotOrd = MkSlotI 

  emptyLeaf = ELeaf M.empty 

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

newtype Handler  slot query deps roots surface state 
  = Handler {getHandler :: Store (Chart deps roots) 
                                 (AlgebraQ query :~> EntityM  deps roots surface state query IO)}

class Forall ks c => All c ks where 
  allC :: Dict (Forall ks c)
  allC = Dict 
instance Forall ks c => All c ks  

type Contains :: Row k -> Row k -> Constraint 
class Subset r2 (r1 .\/ r2) => Contains r1 r2 
instance Subset r2 (r1 .\/ r2) => Contains r1 r2 

data Model ::  SlotData -> Type where 
  Model :: forall surface roots shoots query state deps i 
         . Spec state (Slot surface roots deps query)
        -> Models roots 
        -> Model (Slot surface roots deps query)

data Models :: Row SlotData -> Type where 
  MkModels :: Rec (R.Map Model models) -> Models models 

data Labelled :: Symbol -> Type -> Type where 
  (:=>) :: KnownSymbol l => Label l -> t -> Labelled l t 

class Is rt (R.Map f rk) => MapOf f rt rk where 
  unmap :: Proxy rk 
  unmap = Proxy 

  mapOf :: Dict (rt ~ R.Map f rk)
  mapOf = Dict 

instance rt ~ R.Map f rk => MapOf f rt rk 


data Origin :: SlotData -> Type where 
  MkOrigin :: forall source slot
            . Coherent source slot 
           => TMVar (Entity source)
           -> Origin slot 

unOrigin :: Origin slot -> (forall source. Dict (Coherent source slot) -> TMVar (Entity source) -> r) -> r 
unOrigin (MkOrigin tmv) f = f Dict tmv 
-- going to have to "lift" the constraints somehow 
-- all roots and shoots have to be compatible with whatever the path 
-- to their parent entity ends up being 
-- (deferred this before but b/c need to integrate models at the spec stage, 
-- can't do so now. bleh)

data Chart :: Row SlotData -> Row SlotData -> Type where 
  MkChart :: { mkDeps     :: Proxy deps 
             , mkRoots    :: Proxy roots 
             } -> Chart deps roots  

-- | A `Spec` is the GADT from which an Entity is constructed. 
type Spec :: Type -> SlotData -> Type 
data Spec state slot where
  MkSpec :: forall state query (deps :: Row SlotData) surface roots (shoots :: Row IxSlotData) i source
          . ( WellBehaved roots ) =>
    { initialState   :: state 
    , handleQuery    :: Handler (Slot surface roots deps query) query deps roots surface state
    , renderer       :: Renderer state surface 
    , atlas          :: Chart deps roots
    } -> Spec state (Slot surface roots deps query)
{-
class All (Exists (Extends loc) (Segment 'Begin)) roots => ExtendAll loc roots 
    
type InitPath (slot :: SlotData) = ('Begin :> 'Start slot) 

initPath :: forall (slot :: SlotData) su cs ds q
          . (slot ~ Slot su cs ds q, Locate ('Begin :> 'Start slot) ) 
         => Segment 'Begin ('Begin :> 'Start slot)
initPath = toSeg $ chart @('Begin :> 'Start slot)
-}
-- | `AlgebraQ query a` is a wrapper around a type which records a query algebra. 
--   
--   The first type argument (i.e. `query`) has kind `Type -> Type`
newtype AlgebraQ query a =  Q (Coyoneda query a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, 
--   and a Context which can be read from inside the Prototype monad 
type EvalState :: Row SlotData -> Row SlotData ->  Type -> Type -> (Type -> Type) -> Type
data EvalState    deps roots surface st q where 
  EvalState ::  {
      _entity      :: Spec st (Slot surface roots deps q)
    , _state       :: st
    , _roots       :: ETree roots
    , _surface     :: surface 
    , _environment :: Rec (R.Map STMNode deps) 
    , _origin      :: Origin (Slot surface roots deps q) -- we need this to implement the container meta-component 
    } -> EvalState  deps roots surface st q              
 
-- | Existential wrapper over the EvalState record. 
data ExEvalState :: Row SlotData -> Row SlotData -> Type -> (Type -> Type) -> Type where
  ExEvalState :: EvalState deps roots surface st query 
              -> ExEvalState deps roots surface query  

-- | `Transformer surface query` is a newtype wrapper over `forall x. query x -> IO (x,ExEvalState surface query)`
--  
--   This mainly serves to make reasoning about the EntityStore comonad less painful, and to 
--   signficantly improve the readability of type 
data Transformer deps roots surface query  where 
   Transformer :: 
     (forall x. query x -> IO (x,ExEvalState deps roots surface query  )) -> Transformer deps roots surface query  

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
type EntityStore ::  Row SlotData -> Row SlotData ->Type -> (Type -> Type) -> Type 
type EntityStore deps roots surface  query 
  = Store (ExEvalState deps roots surface  query) (Transformer deps roots surface query)

-- | `Entity surface query` is a newtype wrapper over `TVar (EntityStore surface query)`
--   Mainly for making type signatures easier.
type Entity :: SlotData -> Type 
data Entity slot where 
  Entity :: TVar (EntityStore ds rs su q) -> Entity (Slot su rs ds q)

-- | `Tell query` ==  `() -> query ()` 
type Tell query = () -> query ()

-- | `Request query a` == `(a -> a) -> query a` 
type Request query a = (a -> a) -> query a 

-- don't export the constructor 
type Object :: SlotData -> Type
data Object slot where 
   Object :: Entity (Slot su rs ds q) -> Object (Slot su rs ds q) 

---------------------------
-- Families and constraints 
---------------------------

type SlotConstraint slots = ( -- Forall slots (SlotI Ord)
                            
                              WellBehaved slots 
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

-- don't need this anymore but i don't wanna rewrite the 
-- typeclasses that use it right now 
data Segment :: Path -> Path -> Type where 
  Here   :: forall l start (slot :: SlotData)
         . Segment start (start :> Start slot)

  Parent :: forall start old new    
        . Segment start old 
       -> Segment start (old :> Up new)

  Child :: forall start old new    
        . Segment start old 
       -> Segment start (old :> Down new)

-- A correct by construction witness of connectivity between two entities. 
-- (If one of these exists, the source object "contains" the target object)
data Segment' :: Path -> Type where 
  Here' :: forall i su rs ss ds q 
         . Locate ('Begin :> 'Start (Slot su rs ds q)) 
        => Segment' ('Begin :> 'Start (Slot su rs ds q))

  ChildA' :: forall l l' i su rs ss ds ds' q i' su' rs' ss' q' old 
         . ( -- KnownSymbol l',  
            HasType l' (Slot su' rs' ds' q') rs 
         ) => SlotKey l' rs (Slot su' rs' ds' q')  
           -> Segment' ('Begin :> Start (Slot su rs ds q))
           -> Segment' ('Begin :> Start (Slot su rs ds q) :> Down (l' ':= Slot su' rs' ds' q'))


  ChildB' :: forall l l' i su rs ss ds ds' q i' su' rs' ss' q' old 
         . (-- KnownSymbol l' ,   
             HasType l' (Slot su' rs' ds' q') rs 
         ,   Locate (old :> 'Down (l ':= Slot su rs ds q))
         ,   Locate (old :> 'Down (l ':= Slot su rs ds q) :> Down (l' ':= Slot su' rs' ds' q'))
         ) => SlotKey l' rs (Slot su' rs' ds' q')  
           -> Segment' (old :> 'Down (l ':= Slot su rs ds q))
           -> Segment' (old :> 'Down (l ':= Slot su rs ds q) :> Down (l' ':= Slot su' rs' ds' q'))


{-- IMPORTANT NOTE TO SELF: 
      All of this path reification code was written for the old version where users had to provide 
      path witnesses manually. It could be cut down significantly (and really should be since it is 
      absurdly dense) 

--}

-- Given a Segment' and an entity indexed by the source of the path witnessed by that Segment', 
-- produces the target node 
class Locate (path :: Path) where 
  locate :: Segment' path -> Entity (Source path) -> STM (ENode (Target path))

-- | Appends one path to another, provided they match
type family Connect (parent :: Path) (child :: Path) :: Path where 
  Connect (old :> 'Down (l ':= new)) ('Begin :> 'Start new) = old :> 'Down (l ':= new)
  Connect old (new :> Down (l ':= slot ))  = Connect old new :> Down (l ':= slot )
  Connect old (new :> Up (l ':= slot ))    = Connect old new :> Up (l ':= slot )

-- "term-level" version of Connect 
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
  Normalize ('Begin :> 'Start (Slot su' rs' ds' q') :> Down (l ':= any)) 
    =  'Begin :> 'Start (Slot su' rs' ds' q') :> Down (l ':= (rs' .! l))

  -- D 
  Normalize (old :> 'Down (l' ':= Slot su' rs' ds' q') :> Down (l ':= any))
    =  Normalize (old :> 'Down (l' ':= Slot su' rs' ds' q')) :> Down (l ':= (rs' .! l))

  -- E 
  Normalize ('Begin :> 'Start (Slot su rs ds q) :> 'Down _whatever_ :> Up (l ':= Slot su rs ds q)) 
    =  Normalize ('Begin :> 'Start (Slot su rs ds q))

  -- F
  Normalize (old :> 'Down (l ':= Slot su rs ds q) :> 'Down doesn't_Matter :> Up (l ':= Slot su rs ds q)) 
    =  Normalize (old :> 'Down (l ':= Slot su rs ds q))

  -- G
  Normalize (old :> 'Down (l ':= Slot su rs ds q) :> Up up1 :> Up up2)  
    =  Normalize old 


type CanNormalize path = ( Source path ~ Source (Normalize path)
                         , Target path ~ Target (Normalize path)) 

class ( Target path ~ Target (Normalize path) 
      , Locate (Normalize path))=> 
  Normalizes (path :: Path) where 
        normalize :: Segment 'Begin path -> Segment' (Normalize path)

-- A/B
instance Locate ('Begin :> 'Start (Slot su rs ds q)) => Normalizes ('Begin :> 'Start (Slot su rs ds q)) where
  normalize Here = Here'

-- C 
instance ( KnownSymbol l' 
         , Normalizes ('Begin :> Start (Slot su rs ds q))
         , HasType l' (Slot su' rs' ds' q') rs 
         , Locate (Normalize ('Begin :> Start (Slot su rs ds q) :> 'Down (l' ':= Slot su' rs' ds' q')) )
         )
       => Normalizes ('Begin :> Start (Slot su rs ds q) :> 'Down (l' ':= Slot su' rs' ds' q')) where 
            normalize (Child old) = ChildA' SlotKey (normalize old)

-- D 
instance ( KnownSymbol l' 
         , Normalizes (old :> Down (l ':= Slot su rs ds q))
         , Normalize(old :> Down (l ':= Slot su rs ds q)) ~ (Normalize old :> Down (l ':= Slot su rs ds q))
         , HasType l' (Slot b c d e) rs 
         , Locate (Normalize (old :> Down (l ':= Slot su rs ds q) :> 'Down (l' ':= Slot b c d e)) )
         )
       => Normalizes (old :> Down (l ':= Slot su rs ds q) :> 'Down (l' ':= Slot b c d e)) where 
            normalize (Child old) = ChildB' SlotKey $ normalize old

-- E (start down up)
instance   Normalizes ('Begin :> 'Start (Slot su rs ds q)) 
        => Normalizes ('Begin :> 'Start (Slot su rs ds q) :> 'Down _anything_ :>  Up (l ':= Slot su rs ds q)) where 
  normalize (Parent old) = case old of 
    Child rest -> normalize rest  

-- F (old down up)
instance   Normalizes (old :> 'Down (l ':= Slot su rs ds q)) 
        => Normalizes (old :> 'Down (l ':= Slot su rs ds q) :> 'Down _whatever_ :>  Up (l ':= Slot su rs ds q)) where 
  normalize (Parent old) = case old of 
    Child rest -> normalize rest  

-- G (old down up up)

instance (Normalizes old
        , Target old ~ Target (Normalize old)
        , Target (((old ':> 'Down (l ':= Slot su rs ds q)) ':> 'Up up1) ':> 'Up up2)  ~ Target (Normalize old)
        ) => Normalizes (old :> 'Down (l ':= Slot su rs ds q) :> Up up1 :> Up up2) where 
          normalize (Parent (Parent (Child old))) = normalize old 

class Normalize p ~ p => Normalized p where 
  normalized :: Dict (Normalize p ~ p)
  normalized = Dict  

instance Normalize p ~ p => Normalized p  

class Normalizes p => Charted (p :: Path) where 
  chart :: Segment' (Normalize p) 

-- A/B 
instance  Locate ('Begin :> 'Start (Slot su rs ds q)) 
       => Charted ('Begin :> 'Start (Slot su rs ds q)) where 
  chart = Here' 

-- C (start down)
instance ( KnownSymbol l' 
         , Charted ('Begin :> Start (Slot su rs ds q))
         , HasType l' (Slot su' rs' ds' q') rs 
         , Locate ('Begin :> Start (Slot su rs ds q) :> 'Down (l' ':= Slot su' rs' ds' q'))
         ) => Charted ('Begin :> Start (Slot su rs ds q) :> 'Down (l' ':= Slot su' rs' ds' q')) where 
        chart = ChildA' SlotKey Here' 

-- D (old down down)
instance ( KnownSymbol l' 
         , Charted (old :> Down (l ':= Slot su rs ds q))
         , Normalizes (old :> Down (l ':= Slot su rs ds q))
         , Normalize (old :> Down (l ':= Slot su rs ds q)) ~ (Normalize old :> Down (l ':= Slot su rs ds q))
         , HasType l' (Slot su' rs' ds' q') rs 
         , Locate  ((Normalize old ':> 'Down (l ':= Slot su rs ds q))  ':> 'Down (l' ':= Slot su' rs' ds' q'))
         , Locate (old :> Down (l ':= Slot su rs ds q) :> 'Down (l' ':= Slot su' rs' ds' q'))
         )
       => Charted (old :> Down (l ':= Slot su rs ds q) :> 'Down (l' ':= Slot su' rs' ds' q')) where 
            chart = ChildB' SlotKey (chart @(old :> Down (l ':= Slot su rs ds q)))

-- E (start down up)
instance ( Charted ('Begin :> Start (Slot su rs ds q) )
         , Normalize ('Begin :> Start (Slot su rs ds q)) ~ ('Begin :> Start (Slot su rs ds q))
         , Normalizes ('Begin :> Start (Slot su rs ds q) :> 'Down whocares :> Up (l ':= Slot su rs ds q))
         )
      => Charted ('Begin :> Start (Slot su rs ds q) :> 'Down whocares :> Up (l ':= Slot su rs ds q)) where 
        chart = chart @('Begin :> 'Start (Slot su rs ds q) )

-- F (old down up)        
instance ( Charted (old :> Down (l ':= Slot su rs ds q) ))
      => Charted (old :> Down (l ':= Slot su rs ds q) :> 'Down _any :> Up (l ':= Slot su rs ds q)) where 
        chart = chart @(old :> Down (l ':= Slot su rs ds q) )

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
  Slotify ('Begin :> 'Start (Slot  su cs ds q)) = Slot su cs ds q 
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
  Projections (Slot su rs ds q) = ProjectionsR1 (Slot su rs ds q) rs 

type ProjectionsR1 :: SlotData -> Row SlotData -> [Path] 
type family ProjectionsR1 slot slots where
  ProjectionsR1 (Slot su rs ds q) (R '[]) = '[]
  ProjectionsR1 (Slot su rs ds q) (R lts) = ProjectionsR2 (Slot su rs ds q) lts 

type ProjectionsR2 :: SlotData -> [LT SlotData] -> [Path ]
type family ProjectionsR2 slot lts where 
  ProjectionsR2 (Slot su rs ds q) '[] = '[]

  ProjectionsR2 (Slot su rs ds q) (l ':-> newSlot ': rest) 
    = ('Begin :> 'Start (Slot su rs ds q) :> 'Down (l ':= newSlot)) 
      ': (ConnectEmAll  ('Begin :> 'Start (Slot su rs ds q) :> 'Down (l ':= newSlot)) 
                     (Projections newSlot ) 
      <> ProjectionsR2 (Slot su rs ds q) rest)

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

newtype STMNode :: SlotData -> Type where 
  STMNode :: STM (ENode slot) -> STMNode slot    

class (Charted p, Normalized p, SourceOf p source, TargetOf p target) => ConcretePath source target p where 
  concretePath :: Dict (Charted p, Normalized p, SourceOf p source, TargetOf p target)
  concretePath = Dict 

instance (Charted p, Normalized p, SourceOf p source, TargetOf p target) => ConcretePath source target p

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

data ProxE :: forall k. k -> Type where 
  ProxE :: forall k (a :: k). Top a => ProxE a 

proxE :: forall k (a :: k). ProxE a 
proxE = ProxE  

newtype TopDict a = TopDict (Dict (Top a))

class ( HasSome (ConcretePath source slot) l (Project source)
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

instance ( HasSome (ConcretePath source slot) l (Project source)
         , WellBehaved (Project source)
         ) => Compatible source l slot

mkProxy :: forall slots. ( AllUniqueLabels slots
         , AllUniqueLabels (R.Map Proxy slots)
         , Forall (R.Map Proxy slots) Default
         ) => Proxy slots 
           -> Rec (R.Map Proxy slots)
mkProxy Proxy = R.default' @Default def

class ( ForallL deps (Compatible source)
      , Forall (R.Map Proxy deps) Default
      , WellBehaved deps 
      , WellBehaved (R.Map Proxy deps)
      ) => Compat source deps where 
  compat :: TMVar (Entity source) -> Rec (R.Map STMNode deps) 
  compat tmv = transformWithLabels @SlotData @(Compatible source) @deps @Proxy @STMNode go (mkProxy (Proxy @deps)) 
    where 
      go :: forall (l :: Symbol) (s :: SlotData)
          . Dict (Compatible source l s) 
         -> Proxy s 
         -> STMNode s 
      go Dict Proxy = unify @source @l @s tmv  

instance ( ForallL deps (Compatible source)
      , Forall (R.Map Proxy deps) Default
      , WellBehaved deps 
      , WellBehaved (R.Map Proxy deps)
      ) => Compat source deps 


-- Specialized... existential type (kind) variable binding data types 
-- (we actually need them)
data DepsW :: (Row SlotData -> Constraint) -> SlotData -> Type where 
  DepsW :: forall 
           (c :: Row SlotData -> Constraint)
           (su :: Type) 
           (rs :: Row SlotData) 
           (ds :: Row SlotData) 
           (q :: Type -> Type) 
           (slot :: SlotData)
         . ( c ds
           , slot ~ Slot su rs ds q
         ) => DepsW c slot 

data RootsW :: (Row SlotData -> Constraint) -> SlotData -> Type where 
  RootsW :: forall 
           (c :: Row SlotData -> Constraint)
           (su :: Type) 
           (rs :: Row SlotData) 
           (ds :: Row SlotData) 
           (q :: Type -> Type) 
           (slot :: SlotData)
         . ( c rs
         ,   slot ~ Slot su rs ds q
         ) => RootsW c slot 

-- classes for the above types (need these too)
type SlotD :: (Row SlotData -> Constraint) -> SlotData -> Constraint   
class SlotD c slot where 
  slotD :: DepsW c slot 

instance (c ds) => SlotD c (Slot su rs ds q) where 
  slotD = DepsW 

instance HasDict (c rs) (RootsW c (Slot su rs ds q)) where 
  evidence RootsW = Dict

mkSlotD :: forall c ds su rs q 
         . c ds :- SlotD c (Slot su rs ds q)
mkSlotD = Sub Dict 

mkSlotR :: forall c rs su ds q
         . c rs :- SlotR c (Slot su rs ds q)
mkSlotR = Sub Dict 

unSlotR :: forall c su rs ds q. SlotR c (Slot su rs ds q) :- c rs 
unSlotR = unmapDict go  
  where 
    go :: Dict (SlotR c (Slot su rs ds q)) -> Dict (c rs) 
    go Dict = case slotR :: RootsW c (Slot su rs ds q) of 
          RootsW -> Dict 

type SlotR :: (Row SlotData -> Constraint) -> SlotData -> Constraint 
class SlotR c slot where 
  slotR :: RootsW c slot 

instance c rs => SlotR c (Slot su rs ds q) where 
  slotR = RootsW  

instance HasDict (c ds) (DepsW c (Slot su rs ds q)) where 
  evidence DepsW = Dict 

class ( SlotD (Compat root) slot
      , SlotR (All (SlotD (Compat root))) slot
      , SlotR (All (Coherent root)) slot) => Coherent root slot where 
  coherentR :: Dict (SlotD (Compat root) slot)
  coherentR = Dict 

  coherentD :: Dict (SlotR (All (SlotD (Compat root))) slot)
  coherentD = Dict 

  coherentRec :: Dict (SlotR (All (Coherent root)) slot)
  coherentRec = Dict 

coherentSUQ :: forall su su' q q' root rs ds 
             . Coherent root (Slot su rs ds q) :- Coherent root (Slot su' rs ds q') 
coherentSUQ = unmapDict go 
  where 
    go :: Dict (Coherent root (Slot su rs ds q)) -> Dict (Coherent root (Slot su' rs ds q'))
    go Dict = coherentSUQ' @su @su' @q @q' @root @rs @ds 

coherentSUQ' :: forall su su' q q' root rs ds 
             . Coherent root (Slot su rs ds q) => Dict (Coherent root (Slot su' rs ds q'))
coherentSUQ' = case coherent @root @(Slot su rs ds q) of 
  (d1@Dict,d2@Dict,d3@Dict,rw@RootsW,dw@DepsW) -> case mapDict (mkSlotR @(All (Coherent root)) @rs @su' @ds @q') Dict of 
    dx@Dict ->  case mapDict (mkSlotD @(Compat root) @ds @su' @rs @q') Dict of 
      dy@Dict -> case (coherentD :: Dict (SlotR (All (SlotD (Compat root))) (Slot su rs ds q))) of 
        dz@Dict -> case mapDict (mkSlotR @(All (SlotD  (Compat root))) @rs @su' @ds @q') (mapDict unSlotR d2) of
          dw@Dict -> Dict   

-- ALL THE EVIDENCE
coherent :: forall root slot 
          . Coherent root slot 
         => ( Dict (SlotD (Compat root) slot) 
            , Dict (SlotR (All (SlotD (Compat root))) slot) 
            , Dict (SlotR (All (Coherent root)) slot)
            , RootsW (All (Coherent root)) slot 
            , DepsW  (Compat root) slot)
coherent = case slotD :: DepsW (Compat root) slot of 
  DepsW -> case slotR :: RootsW (All (Coherent root)) slot of 
    RootsW -> case slotR :: RootsW (All (SlotD (Compat root))) slot of 
      RootsW -> (Dict
           ,Dict
           ,Dict
           ,RootsW
           ,DepsW)

instance ( SlotD (Compat root) slot
         , SlotR (All (SlotD (Compat root))) slot 
         , SlotR (All (Coherent root)) slot) => Coherent root slot 

