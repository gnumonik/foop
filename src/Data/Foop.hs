module Data.Foop (
    module Data.Foop.Entity 
  , module Data.Foop.EntityF 
  , module Data.Foop.Eval 
) where

import Data.Foop.Entity
    ( type (:~>),
      NT(..),
      type (~>),
      Prototype(..),
      apNT,
      mkEval,
      mkEntity,
      AlgebraQ(..),
      Spec(..) )



import Data.Foop.EntityF
    ( EntityM(..), EntityF(..), QueryBox(..), MonadLook(..) )


import Data.Foop.Eval ( Entity(..), new, run ) 