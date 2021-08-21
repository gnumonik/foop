{-# LANGUAGE RecordWildCards #-}
module Data.Foop.Eval (new, run, Entity(..)) where


import Control.Monad.Free ( foldFree, retract ) 
import qualified Control.Monad.Trans.State.Strict as ST
import Control.Monad.Trans.Class ( MonadTrans(lift) ) 
import Control.Monad.Reader ( MonadIO(..) ) 
import Data.Kind ( Type ) 
import Control.Comonad.Store
    ( Comonad(extract), store, ComonadStore(seeks), Store ) 
import Control.Concurrent.STM
    ( atomically, newTVarIO, readTVarIO, writeTVar, TVar )
import Data.Foop.Entity
import Data.Foop.EntityF ( EntityM(..), EntityF(..), QueryBox (MkQueryBox))

-- | flips a tuple
fluple :: (a,b) -> (b,a)
fluple (a,b) = (b,a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, and a Context which can be read from inside the Prototype monad 
data EvalState cxt st q act inp outp m 
  = EvalState {
      _entity  :: EntitySpec cxt st q act inp outp m 
    , _state   :: st 
    , _context :: cxt 
  }

data ExEvalState :: (Type -> Type) -> Type ->  Type -> (Type -> Type) -> Type where 
  ExEvalState :: EvalState cxt st q act inp outp m 
              -> ExEvalState  q inp outp m 

withExEval :: forall q inp outp m r  
            . ExEvalState q inp outp m 
            -> (forall cxt st act. EvalState cxt st q act inp outp m -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

new :: forall cxt q i o m 
        . MonadIO m 
       => Prototype cxt q i o m 
       -> cxt 
       -> m (Entity m q i o) 
new (Prototype espec) c  = liftIO (newTVarIO e') >>= \e -> pure $ Entity e 
  where 
    evalSt = initE espec c 

    e' = mkEntity_ evalSt 


initE :: EntitySpec cxt st q act inp outp m 
      -> cxt 
      -> EvalState cxt st q act inp outp m 
initE espec@EntitySpec {..} cxt  
  = EvalState {_entity = espec 
              ,_state = _init ()
              ,_context =  cxt}  

evalAction :: act -> EvalState cxt st q act inp outp m -> EntityM cxt st q act outp m ()
evalAction act e@EvalState {..} =  apNT (_eval _entity) (Action act ())

type EntityStore q i o m      = Store (ExEvalState q i o m) (i -> m (ExEvalState q i o m))

-- This is quite different from Halogen (which is the basis for the foundation of all the Prototype stuff) so, quick explanation: 
-- EntityS is a TVar that holds a store comonad which spits out a *function* from the input to m newEvalState
-- This is kind of a weird construction but because StateT isn't a comonad and we need a StateT from which we can *extract* the state at any time
-- (for queries), -- it serves its purpose
newtype Entity m q i o = Entity {entity :: TVar (EntityStore q i o m)}


mkEntity_ :: forall cxt st q act inp outp m
           . Monad m =>  EvalState cxt st q act inp outp m -> EntityStore q inp outp m 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState q inp outp m -> (inp -> m (ExEvalState q inp outp m))
    go ex@(ExEvalState es@EvalState {..}) = \i -> do  
      let (EntityM ai) = apNT (_eval _entity) (Receive i ())
      let  st          = foldFree (evalF es) ai
      ST.execStateT st ex 

-- | Given an input type for some entity and the entity, run it, returning (maybe) some output 
run :: MonadIO m => i -> Entity m q i o -> m ()
run i (Entity tv) = do
  e <- liftIO $ readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (st) <- f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  liftIO . atomically . writeTVar tv $ newObj -- write new store thingy to tvar 


evalF :: forall cxt' st' q' act' inp' outp' m' a' 
    .  Monad m' 
    => EvalState cxt' st' q' act' inp' outp' m'
    -> EntityF cxt' st' q' act' outp' m' a'
    -> ST.StateT (ExEvalState q' inp' outp' m') m' a' 
evalF EvalState {..} = \case 
  State f -> case f _state of 
    (a,newState) -> do 
        ST.modify $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Ask f   -> pure (f _context)

  Query (MkQueryBox q f)-> case apNT (_eval _entity) (Q q f) of 
    EntityM ef -> foldFree (evalF (EvalState {..})) ef  


