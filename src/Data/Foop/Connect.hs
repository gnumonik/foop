module Data.Foop.Connect where

import Data.Foop.Entity 
import Data.Foop.EntityF 
import Data.Foop.Eval 
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (foldM)
import Data.Functor ((<&>))
import Control.Monad.State.Class 

fanout :: forall t m q x. (Foldable t, MonadIO m) => q x -> t (Entity m q) -> m [x]
fanout i xs = foldM go [] xs  
  where 
    go :: [x] -> Entity m q -> m [x]
    go acc e = run i e <&> (:acc)

fanout_ :: forall t m q x. (Foldable t, MonadIO m) => q x -> t (Entity m q) -> m ()
fanout_ i xs = fanout i xs >> pure ()


data CounterLogic x 
  = GetCount (Int -> x)
  | Tick x

mkCounter :: Prototype () CounterLogic IO 
mkCounter = mkEntity $ MkSpec {
    _init = 0
  , _eval = mkEval runCounterLogic 
  }
 where 
   runCounterLogic :: CounterLogic ~> EntityM () Int CounterLogic IO
   runCounterLogic = \case 
      GetCount f -> do 
        s <- get 
        pure $ f s
      Tick x -> modify' (+1) >> pure x  

getCount counter = request GetCount counter 

tick counter = tell Tick counter 