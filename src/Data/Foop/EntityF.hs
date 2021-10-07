{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Foop.EntityF ( EntityM(..)
                         , EntityF(..)
                         , MonadLook(..)) where

import Control.Monad.Free.Church ( liftF, F(..) ) 
import Control.Monad.State.Class ( MonadState(state) ) 
import Control.Monad.Trans.Class ( MonadTrans(..) ) 
import Control.Monad.Reader ( MonadIO(..), MonadTrans(..) ) 
import Control.Monad.IO.Class ( MonadIO(..) ) 
import Data.Kind ( Type ) 
import Data.Bifunctor ( Bifunctor(first) ) 
import Data.Functor.Coyoneda ( Coyoneda )

class Monad m => MonadLook l m where 
  look :: m l 

type EntityF :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type -> Type 
data EntityF context state query m a 
  = State (state -> (a,state))
  | Lift (m a)
  | Ask (context -> a )
  | Query (Coyoneda query a) 

instance Functor m => Functor (EntityF i state query m) where
  fmap f = \case 
    State k   -> State (first f . k)
    Lift ma   -> Lift (f <$> ma)
    Ask r     -> Ask $ fmap f r
    Query qb  -> Query $ fmap f qb 

newtype EntityM i state query  m a = EntityM (F (EntityF i state query m) a) deriving (Functor, Applicative, Monad)  

instance Functor m => MonadState s (EntityM r s q m) where 
  state f = EntityM . liftF . State $ f 

instance MonadIO m => MonadIO (EntityM r s q m) where 
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM r s q ) where 
  lift = EntityM . liftF . Lift 

instance Functor m => MonadLook l (EntityM l s q m) where 
  look = EntityM . liftF . Ask $ id 

  
