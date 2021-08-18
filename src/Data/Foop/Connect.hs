module Data.Foop.Connect where

import Data.Foop.Entity 
import Data.Foop.EntityF 
import Data.Foop.Eval 

import Data.Profunctor
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (foldM)

fanout :: forall t m i o. (Foldable t, MonadIO m) => i -> t (Entity m i o) -> m [o]
fanout i xs = foldM go [] xs  
  where 
    go :: [o] -> Entity m i o -> m [o]
    go acc e = run i e >>= \case 
      Nothing -> pure acc 
      Just o  -> pure $ o:acc

fanout_ :: forall t m i o. (Foldable t, MonadIO m) => i -> t (Entity m i o) -> m ()
fanout_ i xs = fanout i xs >> pure ()

