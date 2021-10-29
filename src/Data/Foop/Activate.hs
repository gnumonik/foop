{-# LANGUAGE RecordWildCards #-}
module Data.Foop.Activate where

import Data.Foop.Types
import Control.Concurrent.STM
import Data.Kind
import Control.Monad.IO.Class
import Data.Foop.Eval
import Control.Comonad.Store

-- | Takes a prototype and constructs a root entity, which can be queries 
--   directly from the rest of the program.
activate :: Prototype surface query 
        -> IO (Object surface query)
activate p = do 
  e@(Entity tv) <- new_ p 
  pure (Object e)

-- | Run a query against a root entity.
query :: Object surface query 
      -> query x 
      -> IO x 
query (Object e) q = run q e

-- | Like `tell` but for root objects
tell' :: Tell query -> Object surface query -> IO ()
tell' q o = query o (mkTell q) 

-- | Like `request` but for root objects
request' :: Request query a -> Object surface query -> IO a 
request' q o = query o (mkRequest q)

-- | Render a root entity
observe :: Object surface query -> IO surface 
observe (Object e) = renderE e 



{-- 
TO DO: 

1) Add fields to the spec for handlers, add fields to EntityF for output 


2) CLEAN UP THE RENDERING LOGIC! Conceptually it works but it needs a uniform interface 
   and I'm pretty sure it doesn't render every time it needs to. 

2.1) Add a surface field to EvalSpec{..}

3) Think very hard and carefully about some way to construct the render tree
   for an entire object which includes its children and provides a reasonable 
   api for accessing it. It's quite hard with records, might be easier with a dependent or 
   dynamic map? 

I guess 3) isn't strictly necessary cuz halogen can't really do it either but it'd be nice. 
Library is solid even if I can't figure it out though.
--}