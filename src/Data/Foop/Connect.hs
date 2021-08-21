module Data.Foop.Connect where

import Data.Foop.Entity 
import Data.Foop.EntityF 
import Data.Foop.Eval 

import Data.Profunctor
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (foldM)
import Data.Functor ((<&>))

fanout :: forall t m q x. (Foldable t, MonadIO m) => q x -> t (Entity m q) -> m [x]
fanout i xs = foldM go [] xs  
  where 
    go :: [x] -> Entity m q -> m [x]
    go acc e = run i e <&> (:acc)

fanout_ :: forall t m q x. (Foldable t, MonadIO m) => q x -> t (Entity m q) -> m ()
fanout_ i xs = fanout i xs >> pure ()

