{-# LANGUAGE RecordWildCards #-}

module Data.Foop.Entity ( Prototype(..)
                        , EntityQ(..)
                        , EntitySpec(..)
                        , EvalSpec(..)
                        , defaultEval
                        , mkEval
                        , mkEntity
                        , voidE
                        , apNT) where


import Data.Kind ( Type ) 
import Data.Foop.EntityF ( EntityM ) 
import Data.Functor.Coyoneda
import Data.Functor (($>))

data Prototype :: Type -> (Type -> Type) -> Type -> Type -> (Type -> Type) -> Type where 
  Prototype :: EntitySpec r state query action  input output m 
         -> Prototype r query input output m

type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

data  EntityQ query action input a 
  = Receive input a 
  | Action action a 
  | Q (Coyoneda query a) (() -> a)

type EntitySpec :: Type -> Type -> (Type -> Type) -> Type -> Type -> Type -> (Type -> Type) -> Type 
data EntitySpec r state action query input output m where 
  EntitySpec ::
    { _init :: () -> state -- For existential-ey reasons this has to be a function
    , _eval :: EntityQ query action input :~> EntityM r state query action output m  
    } -> EntitySpec r state query action input output m 

newtype HandleQuery r query state action output m 
  = HandleQuery {handleQuery :: forall a. query a -> EntityM r state query action output m (Maybe a) }

runQuery :: HandleQuery r q s a o m 
         -> q x 
         -> EntityM r s q a o m (Maybe x)
runQuery (HandleQuery f) q = f q 

defaultHandleQuery :: forall r query state action output m 
                    . Functor m 
                   => HandleQuery r query state action output m 
defaultHandleQuery = HandleQuery $ const (pure Nothing)  

type EvalSpec :: Type -> Type -> (Type -> Type) -> Type ->  Type -> Type -> (Type -> Type) -> Type 
data EvalSpec r state action query input output m where 
  EvalSpec :: {
              _runAction   :: action -> EntityM r state query action output m ()
            , _receive     :: input -> Maybe action 
            , _handleQuery :: HandleQuery r query state action output m   
           } -> EvalSpec r state query action input output m 

defaultEval :: forall r s q a i o m 
             . Functor m 
            => EvalSpec r s q a i o m 
defaultEval = EvalSpec { _runAction   = const . pure $ ()
                       , _receive     = const Nothing
                       , _handleQuery = defaultHandleQuery}

mkEval :: forall r s q a i o m 
        . Functor m
       => EvalSpec r s q a i o m 
       -> (EntityQ q a i :~> EntityM r s q a o m)
mkEval EvalSpec {..} = NT go 
  where 
    queryHandler :: HandleQuery r q s a o m
    queryHandler = _handleQuery 

    go :: forall x. EntityQ q a i x -> EntityM r s q a o m x
    go = \case 
      Receive i x -> case _receive i of 
        Nothing  -> pure x
        Just act -> _runAction act $> x

      Action action x -> _runAction action $> x 

      Q q f -> unCoyoneda (\g -> fmap (maybe (f ()) g) . runQuery queryHandler) q

    unCoyoneda :: forall (f :: Type -> Type) (a :: Type) (r :: Type)
                . (forall (b :: Type). (b -> a) -> f b -> r)
               -> Coyoneda f a 
               -> r 
    unCoyoneda f (Coyoneda ba fb) = f ba fb 

mkEntity :: EntitySpec r s q a i o m 
         -> Prototype r q i o m 
mkEntity e = Prototype e 

voidE :: forall r s q a o m. Functor m => EntityM r s q a o m () -> EntityM r s q a o m (Maybe o)
voidE m = m >> pure Nothing