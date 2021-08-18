module Data.Foop (
    module Data.Foop.Entity 
  , module Data.Foop.EntityF 
  , module Data.Foop.Eval 
) where

import Data.Foop.Entity
    ( EntitySpec(..),
      EntityQ(..),
      defaultEval,
      mkEval,
      mkEntity,
      voidE,
      Prototype(..) )

import Data.Foop.EntityF
    ( EntityM(..), EntityF(..), withContext, getContext )

import Data.Foop.Eval ( Entity(..), new, run ) 