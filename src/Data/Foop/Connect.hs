module Data.Foop.Connect where

import Data.Foop
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad 
import Data.Functor ((<&>))
import Control.Monad.State.Class 
import Data.Row
import Data.Proxy 
import Control.Concurrent.STM 


testCounter :: IO () 
testCounter = do 
  counter <- activate mkCounter ()
  count <- atomically $ do 
              replicateM_ 10 (tick counter)
              printCount counter 
              replicateM_ 100 (tick counter)
              printCount counter 
              replicateM_ 1000 (tick counter)
              printCount counter
              getCount counter 
  print count 


type (:=) a b = a .== b 

data CounterLogic x 
  = GetCount (Int -> x)
  | Tick x
  | PrintCount x 

mkCounter :: Prototype Empty String () CounterLogic 
mkCounter = prototype $ MkSpec {
    initialState = 0
  , handleQuery = queryHandler runCounterLogic 
  , render = Just . show 
  , slots = emptySlots 
  }
 where 
   runCounterLogic :: CounterLogic ~> EntityM Empty () Int CounterLogic STM
   runCounterLogic = \case 
      GetCount f -> f <$> get 

      Tick x -> modify' (+1) >> pure x  
      
      PrintCount x -> do 
        s <- get 
        _ <- liftIO (print s)
        pure x 

printCount :: Object surface CounterLogic -> STM ()
printCount e = query e (mkTell PrintCount)

getCount :: Object surface CounterLogic -> STM Int
getCount e = query e (mkRequest GetCount)

tick :: Object surface CounterLogic -> STM ()
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