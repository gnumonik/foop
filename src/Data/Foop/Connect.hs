module Data.Foop.Connect where

import Data.Foop
import Control.Monad.IO.Class (MonadIO)
import Control.Monad 
import Data.Functor ((<&>))
import Control.Monad.State.Class 
import Data.Row


testCounter :: Int -> IO () 
testCounter n = do 
  counter <- initObject mkCounter ()
  replicateM_ n (tick counter)
  count <- getCount counter 
  print count 


data CounterLogic x 
  = GetCount (Int -> x)
  | Tick x

mkCounter :: Prototype Empty Int () CounterLogic IO 
mkCounter = prototype $ MkSpec {
    initialState = 0
  , handleQuery = queryHandler runCounterLogic 
  , render = Just
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