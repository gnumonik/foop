{-# LANGUAGE RecordWildCards #-}

module Data.Foop.Entity ( Prototype(..)
                        , EntityQ(..)
                        , EntitySpec(..)
                        , EvalSpec(..)
                        , defaultEval
                        , mkEval
                        , mkEntity
                        , voidE) where


import Data.Kind ( Type ) 
import Data.Foop.EntityF ( EntityM ) 


data Prototype :: Type -> Type -> Type -> (Type -> Type) -> Type where 
  Prototype :: EntitySpec r state action  input output m 
         -> Prototype r input output m


type (~>) m n = (forall a. m a -> n a) 

data NT :: (Type -> Type) -> (Type -> Type) -> Type where 
  NT :: forall m n. (forall a. m a -> n a) -> NT m n 

type (:~>) m n = NT m n 

apNT :: m :~> n -> m a -> n a 
apNT (NT f) = f 

data  EntityQ action input 
  = Receive input 
  | Action action 

type EntitySpec :: Type -> Type -> Type -> Type -> Type -> (Type -> Type) -> Type 
data EntitySpec r state action  input output m where 
  EntitySpec ::
              { _init :: () -> state -- For existential-ey reasons this has to be a function
              , _eval :: EntityQ action input -> EntityM r state action output m (Maybe output) 
              } -> EntitySpec r state action input output m 

type EvalSpec :: Type -> Type -> Type ->  Type -> Type -> (Type -> Type) -> Type 
data EvalSpec r state action  input output m where 
  EvalSpec :: {
              _runAction  :: action -> EntityM r state action output m (Maybe output)
            , _receive    :: input -> Maybe action 
           } -> EvalSpec r state action  input output m 

defaultEval :: forall r s a i o m 
             . Functor m 
            => EvalSpec r s a i o m 
defaultEval = EvalSpec { _runAction  = const . pure $ Nothing
                       , _receive    = const Nothing}

mkEval :: forall r s a i o m 
        . Functor m
       => EvalSpec r s a i o m 
       -> EntityQ a i -> EntityM r s a  o m (Maybe o)
mkEval EvalSpec {..} =  go 
  where 
    go :: EntityQ a i -> EntityM r s a  o m (Maybe o)
    go = \case 
      Receive i -> case _receive i of 
        Nothing  -> pure Nothing 
        Just act -> _runAction act 

      Action action -> _runAction action 

mkEntity :: EntitySpec r s a i o m 
         -> Prototype r i o m 
mkEntity e = Prototype e 

voidE :: forall r s a o m. Functor m => EntityM r s a o m () -> EntityM r s a o m (Maybe o)
voidE m = m >> pure Nothing