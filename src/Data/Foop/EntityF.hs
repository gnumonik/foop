{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Foop.EntityF ( EntityM(..)
                         , EntityF(..)
                         , MonadLook(..)
                         , type SlotData) where

import Control.Monad.Free.Church ( liftF, F(..) ) 
import Control.Monad.State.Class ( MonadState(state) ) 
import Control.Monad.Trans.Class ( MonadTrans(..) ) 
import Control.Monad.Reader ( MonadIO(..), MonadTrans(..) ) 
import Control.Monad.IO.Class ( MonadIO(..) ) 
import Data.Kind ( Type, Constraint ) 
import Data.Bifunctor ( Bifunctor(first) ) 
import Data.Functor.Coyoneda ( Coyoneda )
import Data.Row 
import Data.Constraint 

type SlotData = (Type,Type, Type -> Type, Type -> Type)

class Monad m => MonadLook l m where 
  look :: m l 

type EntityF :: Row SlotData -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
data EntityF slots context state query m a where 
  State :: (state -> (a,state)) -> EntityF slots context state query m a
  Lift  :: (m a) -> EntityF slots context state query m a
  Ask   :: (context -> a) -> EntityF slots context state query m a
  Query :: (Coyoneda query a) -> EntityF slots context state query m a
 


instance Functor m => Functor (EntityF slots i state query m) where
  fmap f = \case 
    State k   -> State (first f . k)
    Lift ma   -> Lift (f <$> ma)
    Ask r     -> Ask $ fmap f r
    Query qb  -> Query $ fmap f qb 


newtype EntityM slots i state query  m a = EntityM (F (EntityF slots i state query m) a) deriving (Functor, Applicative, Monad)  

instance Functor m => MonadState s (EntityM slots r s q m) where 
  state f = EntityM . liftF . State $ f 

instance MonadIO m => MonadIO (EntityM slots r s q m) where 
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM slots r s q ) where 
  lift = EntityM . liftF . Lift 

instance Functor m => MonadLook l (EntityM slots l s q m) where 
  look = EntityM . liftF . Ask $ id 

  
