{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Example where

import Data.Foop

import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad ( replicateM_ ) 
import Data.Functor ((<&>))
import Control.Monad.State.Class ( MonadState(get), modify' ) 
import Data.Row ( Empty, type (.==), type (.+), (.==) ) 
import Data.Proxy (Proxy (Proxy)) 
import Control.Concurrent.STM () 
import Data.Row.Internal
import Data.Default
import qualified Data.Constraint.Forall as DC  
import Data.Constraint
import Data.Foop.Slot
import qualified Data.Row.Records as R
import Data.Kind
import Data.Foop.Exists

-- Example #1: A Simple Counter 

-- | This is the data type that records the query logic for 
--   our counter object. 
-- 
--   **GetCount** is a *Request* for an *Int* 
--   because the last argument to the **GetCount** constructor 
--   is a function of type *Int -> x*. 
--
--   **Tick**, **Reset**, and **PrintCount** are *Tell*s because 
--   the last argument to each of these constructors is 
--   the type variable *x*.
data CounterLogic x 
  = GetCount (Int -> x)
  | Tick x
  | Reset x 
  | PrintCount x 

returning :: Monad m => x -> m () -> m x
returning x m = m >> pure x 

-- | *counter* is a simple *Prototype* for an *Entity*. 
--
--   The *surface* of *counter* is *String*; when we render 
--   an Entity made from this prototype, it will produce a String. 
--
--   Note that GHC can infer the types here. 

-- counter :: Prototype String CounterLogic 

type TOP :: forall k. k -> Constraint 
class TOP c 
instance TOP c 



testDeps = MkPaths (#here .== Here @'Begin @MySlot)

counter =  Model $ MkSpec {
    initialState = 0 :: Int
  , handleQuery  = mkQHandler_ runCounterLogic 
  , renderer     = mkSimpleRender show  -- this is a function from the component's state to its surface
  , slots        = emptySlots 
  }
 where 
  runCounterLogic =  \case 
    GetCount f -> f <$> get 

    Tick x -> returning x $ modify' (+1)   

    Reset x -> do 
      -- badoop <- observe_ (Start ||> Up) (const ())
    -- BoxedContext t <- lewk 
    -- let hm = t ^? deep
    -- _ <- open' (deep) >> pure () 
      pure x 

    PrintCount x -> returning x $ do 
      s <- get 
      liftIO (print s)

-- If we wanted to use our counter Entity as a Root Entity, 
-- that is, a top-level entity which does not have parents and against which 
-- we can directly run queries, we might create "methods" such as these,
-- which use request' and tell'

printCount' :: Object (Slot () s cs CounterLogic) -> IO ()
printCount' = tell' PrintCount 

getCount' :: Object (Slot () s cs CounterLogic) -> IO Int
getCount' = request' GetCount 

tick' :: Object (Slot () s cs CounterLogic) -> IO ()
tick' = tell' Tick  

reset' :: Object (Slot () s cs CounterLogic) -> IO ()
reset' = tell' Reset

-- And we could use them like so: 

testCounter :: IO () 
testCounter = do 
  counter <- activate counter 
  replicateM_ 10 (tick' counter)
  printCount' counter 
  replicateM_ 100 (tick' counter)
  printCount' counter 
  replicateM_ 1000 (tick' counter)
  printCount' counter
  reset' counter 
  replicateM_ 100000 (tick' counter)
  getCount' counter >>= print 


-- If, alternatively, we wished to use our counter object as a child entity of 
-- some other component, we could do so in the following manner. These will work in 
-- the monadic context of any entity which has at least one slot containing our 
-- counter entity 

-- Note that to use these, we will need a type application of the symbol 
-- which serves as the slot's label.

-- Also note that the constraints required to make this work are *quite* involved, and although
-- GHC can and will infer the type signature, your code might be prettier if you just left it off :)  


printCount i = tell i PrintCount 

getCount i = request i GetCount 

tick i = tell i Tick 

rest i = tell i Reset 

data CountersLogic x where 
  NewCounterA    :: String -> x -> CountersLogic x 

  NewCounterB    :: Char -> x -> CountersLogic x

  DeleteCounter  :: Either String Char -> x -> CountersLogic x 

  TellCounter    :: Either String Char -> Tell CounterLogic -> x -> CountersLogic x 

  RequestCounter :: Either String Char -> Request CounterLogic a -> (Maybe a -> x) -> CountersLogic x 

type CountersSlots = "counterA" .== Slot String String Empty CounterLogic 
                  .+ "counterB" .== Slot Char String Empty CounterLogic 

--mkCounters :: Prototype String CountersLogic

mkIndexed :: forall i root deps state surface slots query
           . Spec deps state (Slot i surface slots query)
          -> Spec deps state (Slot i surface slots query)
mkIndexed = id 

mkRoot :: Spec deps state (Slot i surface slots query)
       -> Spec deps state (Slot i surface slots query)
mkRoot = id 

instSlots :: forall slots i deps state surface query
       . Spec deps state (Slot i surface slots query)
      -> Spec deps state (Slot i surface slots query)
instSlots = id 

counters :: (Exists
   (Rooted
      (Slot
         i1
         String
         ('R
            '[ "counterA"
               ':-> '(String, String, RenderTree Empty, CounterLogic),
               "counterB" ':-> '(Char, String, RenderTree Empty, CounterLogic)])
         CountersLogic))
   (PathFinder 'Begin)
   (PathFinder start (start ':> 'Leaf_ (Slot i2 su cs q))),
 Ord i2) =>
  Model
    ('R
      '[ "here"
          ':-> PathFinder start (start ':> 'Leaf_ (Slot i2 su cs q))])
    (Slot
      i1
      String
      ('R
          '[ "counterA"
            ':-> '(String, String, RenderTree Empty, CounterLogic),
            "counterB" ':-> '(Char, String, RenderTree Empty, CounterLogic)])
      CountersLogic)
counters =  Model $ MkSpec {
    initialState = ()
  , handleQuery = mkQHandler myPaths runCounters 
  , renderer = mkSimpleRender show
  , slots = Proxy @CountersSlots
  }
 where
   myPaths = MkPaths $ #here .== Here 

   runCounters myPaths = \case 
    NewCounterA n x -> do 
      create @"counterA" n counter
      pure x  

    NewCounterB n x -> do 
      create @"counterB" n counter
      pure x  

    DeleteCounter k x -> do  
      either (delete @"counterA") (delete @"counterB") k 
      pure x 

    TellCounter k t x  -> do  
    --  hm <- observe_ #here id
      either (\i -> tell @"counterA" i t) (\i -> tell @"counterB" i t) k 
      pure x  

    RequestCounter k r f -> do  
      output <- either (\i -> request @"counterA" i r) (\i -> request @"counterB" i r) k 
      pure (f output) 

    

    

    


