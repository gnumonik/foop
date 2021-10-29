{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}

{--

Module organization sucks but the types are too mutually dependent to 
avoid placing them all in one module. Oh well. 
--}

module Data.Foop  ( EntityM(..)
                  , type SlotData
                  , SlotBox(..)
                  , type Slot 
                  , type SlotOrdC 
                  , Prototype(..)
                  , type (~>)
                  , AlgebraQ(..)
                  , Spec(..)
                  , queryHandler
                  , type ChildStorage 
                  , type MkStorage 
                  , type ChildC 
                  , type StorageConstraint 
                  , type RenderConstraint 
                  , type MkRenderTree 
                  , type Tell 
                  , type Request  
                  , type Entity 
                  , mkTell 
                  , mkRequest
                  , tell'
                  , tell 
                  , tellAll
                  , request' 
                  , request 
                  , requestAll 
                  , delete 
                  , create
                  , emptySlots
                  , prototype
                  , mkSimpleRender
                  , activate
                  , query
                  , type Object) where

import Data.Foop.Types 
import Data.Foop.Eval 
import Data.Foop.Prototype 
import Data.Foop.Activate 