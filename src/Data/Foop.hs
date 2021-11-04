{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

{--

Module organization sucks but the types are too mutually dependent to 
avoid placing them all in one module. Oh well. 
--}

module Data.Foop  (module Data.Foop.Types 
                  ,module Data.Foop.Eval 
                  ,module Data.Foop.Prototype
                  ,module Data.Foop.Activate) where

import Data.Foop.Types 
import Data.Foop.Eval 
import Data.Foop.Prototype 
import Data.Foop.Activate 