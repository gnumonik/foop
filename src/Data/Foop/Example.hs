{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Example where

import Data.Foop

import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad ( replicateM_ ) 
import Data.Functor ((<&>))
import Control.Monad.State.Class ( MonadState(get), modify' ) 
import Data.Row ( Empty, type (.==), type (.+) ) 
import Data.Proxy (Proxy (Proxy)) 
import Control.Concurrent.STM () 
import Data.Row.Internal
import Data.Default
import qualified Data.Constraint.Forall as DC  
import Control.Monad.Identity
import Data.Constraint
import Data.Foop.Slot
import Control.Lens (view, (^?))


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


defaultSpec = MkSpec () (queryHandler $ \(Identity x) -> pure x) (mkSimpleRender (const ())) emptySlots








counter =  Model $ MkSpec {
    initialState = 0 :: Int
  , handleQuery  = queryHandler runCounterLogic 
  , renderer     = mkSimpleRender show  -- this is a function from the component's state to its surface
  , slots        = emptySlots 
  }

-- runCounterLogic :: CounterLogic ~> EntityM Empty Int CounterLogic IO







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


{--
See what I mean? :p This mostly amounts to "Ord i and no duplicate labels" as most of the Row Types 
constructed by the type families cannot be constructed in such a way as to fail to satisfy most of 
these constraints, but *proving* that to GHC is... not how I wanna spend my weekend

printCount :: (Data.Row.Internal.AllUniqueLabels (MkStorage slots),
              Data.Row.Internal.AllUniqueLabels slots,
              Data.Row.Internal.AllUniqueLabels (MkRenderTree slots),
              Data.Row.Internal.Forall slots Data.Row.Internal.Unconstrained1,
              Data.Row.Internal.Forall slots SlotOrdC,
              Data.Row.Internal.Forall
                (MkStorage slots) Data.Row.Internal.Unconstrained1,
              Data.Row.Internal.Forall (MkStorage slots) Data.Default.Class.Default,
              Data.Row.Internal.Forall
                (MkRenderTree slots) Data.Row.Internal.Unconstrained1,
              Data.Row.Internal.Forall (MkRenderTree slots) Data.Default.Class.Default,
              GHC.TypeLits.KnownSymbol lbl, 
              Ord i,
              (MkStorage slots Data.Row.Internal..! lbl) ~ Data.Map.Internal.Map i (Data.Foop.Types.Entity r CounterLogic),
              (MkRenderTree slots Data.Row.Internal..! lbl) ~ Data.Map.Internal.Map i r) 
          =>
i -> EntityM slots state q IO () --}


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




counters = Model $  MkSpec {
    initialState = ()
  , handleQuery = queryHandler runCounters 
  , renderer = mkSimpleRender show
  , slots = Proxy @CountersSlots
  }
 where
  -- runCounters ::  CountersLogic ~> EntityM CountersSlots () CountersLogic IO 
   runCounters = \case 
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
      either (\i -> tell @"counterA" i t) (\i -> tell @"counterB" i t) k 
      pure x  

    RequestCounter k r f -> do  
      output <- either (\i -> request @"counterA" i r) (\i -> request @"counterB" i r) k 
      pure (f output) 

    

    

    


