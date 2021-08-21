{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Foop.EntityF ( EntityM(..)
                         , EntityF(..)
                         , withContext
                         , getContext
                         , QueryBox(..)) where



import Control.Monad.Free ( liftF, Free ) 
import Control.Monad.State.Class ( MonadState(state) ) 
import Control.Monad.Trans.Class ( MonadTrans(..) ) 
import Control.Monad.Reader 
import Control.Monad.IO.Class ( MonadIO(..) ) 
import Data.Kind ( Type ) 
import Data.Bifunctor ( Bifunctor(first) ) 
import Data.Functor.Coyoneda
import Data.Profunctor (Profunctor(rmap))


{-- Need to add a Query system but it has to be different from  
    the way it works in Halogen b/c we're not concerned w/ slots 

  The problem w/ the current input/output system is that we don't have a way of matching 
  specific inputs w/ specific outputs. We can pattern match, but that's not ideal. 

  The Haskell-ized versions of Halogen's query-related types are: 

  data ObjectQ query action input a 
  = Initialize a 
  | Finalize a 
  | Receive input a 
  | Action action a
  | Query (Coyoneda query a) (() -> a) deriving Functor 

  data CQBox :: Row Type -> Type -> Type where 
  CQBox :: forall k ps  a g o f b i 
         . CQ ps g o a f b i -> CQBox ps a 

  data CQ :: Row Type -> (Type -> Type) -> Type -> Type -> (Type -> Type) -> Type -> Type -> Type  where 
    CQ :: (forall slot m. Applicative m => (slot g o i -> m (Maybe b)) -> Storage' ps slot -> m (f b))
        -> (g b)
        -> (f b -> a)
        -> CQ ps g o a f b i 

  Coyoneda :: (b -> a) -> f b -> Coyoneda f a	 
   -- so  in Coyoneda query a: 
              query :: (Type -> Type) ~ (f _) 

      so (just to remind myself): Query is a type constructor that types one type variable 
                                  argument. 
--}

data QueryBox :: (Type -> Type) -> Type -> Type where 
  MkQueryBox :: Coyoneda f a -> (() -> a) -> QueryBox f a 

instance Functor (QueryBox f) where 
  fmap f (MkQueryBox q g) = MkQueryBox (fmap f q) (rmap f g) 

type EntityF :: Type -> Type -> (Type -> Type) -> Type -> Type -> (Type -> Type) -> Type -> Type 
data EntityF context state query action output m a 
  = State (state -> (a,state))
  | Lift (m a)
  | Ask (context -> a )
  | Query (QueryBox query a) 

instance Functor m => Functor (EntityF i state query action output m) where
  fmap f = \case 
    State k   -> State (first f . k)
    Lift ma   -> Lift (f <$> ma)
    Ask r     -> Ask $ fmap f r
    Query qb  -> Query $ fmap f qb 

newtype EntityM i state query action  output m a = EntityM (Free (EntityF i state query action output m) a) deriving (Functor, Applicative, Monad)  

instance Functor m => MonadState s (EntityM r s q a o m) where 
  state f = EntityM . liftF . State $ f 

instance MonadIO m => MonadIO (EntityM r s q a o m) where 
  liftIO m = EntityM . liftF . Lift . liftIO $ m

instance MonadTrans (EntityM r s q a o) where 
  lift = EntityM . liftF . Lift 

withContext :: Functor m => (r -> x) -> EntityM r s q a o m x
withContext f =  EntityM . liftF . Ask $ \r -> f r

getContext :: Functor m => EntityM r s q a o m r 
getContext = EntityM . liftF . Ask $ id 


type Tell f = () -> f ()

mkTell :: forall f. Tell f -> f ()
mkTell action = action ()


tell :: Functor m => Tell q -> EntityM r s q a o m ()
tell q = EntityM . liftF . Query $ MkQueryBox (liftCoyoneda $ q ()) (const ())

type Request f a = (a -> a) -> f a 

mkRequest :: forall f a. Request f a -> f a 
mkRequest req = req id 

request :: Functor m => Request q x -> EntityM r s q a o m x
request q = EntityM . liftF . Query $ MkQueryBox (liftCoyoneda $ q id) ()
