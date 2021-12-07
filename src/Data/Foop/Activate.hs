{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Activate where

import Data.Foop.Types
import Control.Concurrent.STM
import Data.Kind
import Control.Monad.IO.Class
import Data.Foop.Eval
import Control.Comonad.Store
import Data.Foop.Slot
import Data.Proxy
import qualified Data.Constraint.Forall as DC
import Data.Constraint
import Data.Row
import Data.Row.Dictionaries

-- | Takes a prototype and constructs a root entity, which can be queries 
--   directly from the rest of the program.
activate :: forall surface children query deps 
          .  Coherent (Slot surface children deps query) (Slot surface children deps query) 
         => Model (Slot surface children deps query)
         -> IO (Object (Slot  surface children deps query))
activate (Model espec@MkSpec{..} ms) =  do 
      let rendered = render renderer initialState
      e@(Entity tv) <- new_' espec  ms rendered 
      pure $ Object e 

-- | Run a query against a root entity.
query :: Object (Slot su cs ds q)
      -> q x 
      -> IO x 
query (Object e) q = run q e

-- | Like `tell` but for root objects
tell' :: Tell q -> Object (Slot s cs ds q) -> IO ()
tell' q o = query o (mkTell q) 

-- | Like `request` but for root objects
request' :: Request q a -> Object (Slot s cs ds q) -> IO a 
request' q o = query o (mkRequest q)

{-
-- | Render a root entity
observe :: Object (Slot () s cs q) -> IO (ENode (Slot () s cs q))
observe (Object e) = atomically $ observeE e 
-}


