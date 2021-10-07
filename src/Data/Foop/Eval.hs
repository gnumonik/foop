{-# LANGUAGE RecordWildCards #-}
module Data.Foop.Eval (new, run, Entity(..), type Tell, type Request, tell, request) where

{-- need to not export run --}

import Control.Monad.Free.Church ( foldF, retract ) 
import qualified Control.Monad.Trans.State.Strict as ST
import Control.Monad.Trans.Class ( MonadTrans(lift) ) 
import Control.Monad.Reader ( MonadIO(..) ) 
import Data.Kind ( Type, Constraint ) 
import Control.Comonad.Store
    ( Comonad(extract), store, ComonadStore(seeks), Store ) 
import Control.Concurrent.STM
    ( atomically, newTVarIO, readTVarIO, writeTVar, TVar )
import Data.Foop.Entity
    ( apNT, AlgebraQ(Q), Prototype(..), Spec(..) )
import Data.Foop.EntityF ( EntityF(..), EntityM(EntityM) ) 
import Data.Functor.Coyoneda

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, and a Context which can be read from inside the Prototype monad 
data EvalState cxt st q m 
  = EvalState {
      _entity  :: Spec cxt st q m 
    , _state   :: st 
    , _context :: cxt 
  }

data ExEvalState :: (Type -> Type) -> (Type -> Type) -> Type where 
  ExEvalState :: EvalState cxt st q  m 
              -> ExEvalState q m 

withExEval :: forall q m r  
            . ExEvalState q m 
            -> (forall cxt st. EvalState cxt st q m -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

new :: forall cxt q m 
        . MonadIO m 
       => Prototype cxt q  m 
       -> cxt 
       -> m (Entity m q ) 
new (Prototype espec) c  = liftIO (newTVarIO e') >>= \e -> pure $ Entity e 
  where 
    evalSt = initE espec c 

    e' = mkEntity_ evalSt 


initE :: Spec cxt st q m 
      -> cxt 
      -> EvalState cxt st q m 
initE espec@MkSpec {..} cxt  
  = EvalState {_entity = espec 
              ,_state = _init 
              ,_context =  cxt}  

newtype Transformer q m = Transformer {transform :: forall x. q x -> m (x,ExEvalState q m)}

type EntityStore q  m      = Store (ExEvalState q  m) (Transformer q m)

-- This is quite different from Halogen (which is the basis for the foundation of all the Prototype stuff) so, quick explanation: 
-- EntityS is a TVar that holds a store comonad which spits out a *function* from the input to m newEvalState
-- This is kind of a weird construction but because StateT isn't a comonad and we need a StateT from which we can *extract* the state at any time
-- (for queries), -- it serves its purpose
newtype Entity m q = Entity {entity :: TVar (EntityStore q m)}


mkEntity_ :: forall cxt st q m
           . Monad m =>  EvalState cxt st q  m -> EntityStore q  m 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState q m -> Transformer q m
    go ex@(ExEvalState es@EvalState {..}) = Transformer $ \qx -> do  
      let (EntityM ai) = apNT (_eval _entity) (Q . liftCoyoneda $ qx)
      let  st          = foldF (evalF es) ai
      ST.runStateT st ex
      

-- | Given an input type for some entity and the entity, run it, returning (maybe) some output 
run :: forall x m q. MonadIO m => q x -> Entity m q -> m x
run i (Entity tv) = do
  e <- liftIO $ readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (x,st) <- transform f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  liftIO . atomically . writeTVar tv $ newObj -- write new store thingy to tvar 
  pure x 

type Tell q = () -> q ()

tell :: forall m q. MonadIO m => Tell q -> Entity m q -> m ()
tell q = run (q ())

type Request q a = (a -> a) -> q a 

request :: forall m q x. MonadIO m => Request q x -> Entity m q -> m x 
request q = run (q id) 

evalF :: forall cxt' st' q'  m' a' 
    .  Monad m' 
    => EvalState cxt' st' q'  m'
    -> EntityF cxt' st' q' m' a'
    -> ST.StateT (ExEvalState q' m') m' a' 
evalF EvalState {..} = \case 
  State f -> case f _state of 
    (a,newState) -> do 
        ST.modify $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Ask f   -> pure (f _context)

  Query q -> case apNT (_eval _entity) (Q q ) of 
    EntityM ef -> foldF (evalF (EvalState {..})) ef  







