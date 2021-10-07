module Data.Foop (
    module Data.Foop.Entity 
  , module Data.Foop.EntityF 
  , module Data.Foop.Eval 
) where

import Data.Foop.Entity
    ( apNT,
      mkEntity,
      mkEval,
      type (:~>),
      AlgebraQ(..),
      NT(..),
      Prototype(..),
      Spec(..),
      type (~>) )

import Data.Foop.EntityF
    ( EntityF(..), EntityM(..), MonadLook(..) )

import Data.Foop.Eval
    ( Request, Tell, Entity(..), new, run, tell, request )
