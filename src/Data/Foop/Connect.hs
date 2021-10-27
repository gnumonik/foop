module Data.Foop.Connect where

import Data.Foop
import Control.Monad.IO.Class (MonadIO)
import Control.Monad 
import Data.Functor ((<&>))
import Control.Monad.State.Class 
import Data.Row
import Data.Proxy 

testCounter :: Int -> IO () 
testCounter n = do 
  let counter = initObject mkCounter ()
  replicateM_ n (tick counter)
  count <- getCount counter 
  print count 


type (:=) a b = a .== b 

data CounterLogic x 
  = GetCount (Int -> x)
  | Tick x

mkCounter :: Prototype Empty String () CounterLogic IO 
mkCounter = prototype $ MkSpec {
    initialState = 0
  , handleQuery = queryHandler runCounterLogic 
  , render = Just . show 
  , slots = emptySlots 
  }
 where 
   runCounterLogic :: CounterLogic ~> EntityM Empty () Int CounterLogic IO
   runCounterLogic = \case 
      GetCount f -> f <$> get 
      Tick x -> modify' (+1) >> pure x  

getCount :: forall m surface. MonadIO m => Object surface m CounterLogic -> m Int
getCount e = query e (mkRequest GetCount)

tick :: forall m surface. MonadIO m => Object surface m CounterLogic -> m ()
tick e = query e (mkTell Tick)  
{--
data CountersLogic x 
  = NewCounter Int x 
  | TickCounter Int x 
  | DeleteCounter Int x 

mkCounters = prototype $ MkSpec {
    initialState = ()
  , handleQuery = queryHandler runCounters 
  , render = undefined 
  , slots = Proxy @("counter" := MkSlot Int Int CounterLogic IO)
  }
 where
   runCounters = \case 
    NewCounter n x -> do 
      create (new)
--}