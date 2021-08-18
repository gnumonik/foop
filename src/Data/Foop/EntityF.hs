{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Foop.EntityF (EntityM(..), EntityF(..), withContext, getContext) where



import Control.Monad.Free ( liftF, Free ) 
import Control.Monad.State.Class ( MonadState(state) ) 
import Control.Monad.Trans.Class ( MonadTrans(..) ) 
import Control.Monad.Reader 
import Control.Monad.IO.Class ( MonadIO(..) ) 
import Data.Kind ( Type ) 
import Data.Bifunctor ( Bifunctor(first) ) 

type EntityF :: Type -> Type -> Type -> Type -> (Type -> Type) -> Type -> Type 
data EntityF i state action output m a 
  = State (state -> (a,state))
  | Lift (m a)
  | Read (i -> a )

instance Functor m => Functor (EntityF i state action output m) where
  fmap f = \case 
    State k   -> State (first f . k)
    Lift ma   -> Lift (f <$> ma)
    Read r    -> Read $ fmap f r

newtype EntityM i state action  output m a = EntityM (Free (EntityF i state action output m) a) deriving (Functor, Applicative, Monad)  

instance Functor m => MonadState s (EntityM r s a  o m) where 
  state f = EntityM . liftF . State $ f 

instance MonadIO m => MonadIO (EntityM r s a  o m) where 
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM r s a o) where 
  lift = EntityM . liftF . Lift 

withContext :: Functor m => (r -> x) -> EntityM r s a o m x
withContext f =  EntityM . liftF . Read $ \r -> f r

getContext :: Functor m => EntityM r s a o m r 
getContext = EntityM . liftF . Read $ id 
