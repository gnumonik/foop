{-# LANGUAGE RecordWildCards #-}
module Data.Foop.Eval (new, run, Entity(..)) where


import Control.Monad.Free ( foldFree ) 
import qualified Control.Monad.Trans.State.Strict as ST
import Control.Monad.Trans.Class ( MonadTrans(lift) ) 
import Control.Monad.Reader ( MonadIO(..) ) 
import Data.Kind ( Type ) 
import Control.Comonad.Store
    ( Comonad(extract), store, ComonadStore(seeks), Store ) 
import Control.Concurrent.STM
    ( atomically, newTVarIO, readTVarIO, writeTVar, TVar )
import Data.Foop.Entity
import Data.Foop.EntityF ( EntityM(..), EntityF(..) )



-- | flips a tuple
fluple :: (a,b) -> (b,a)
fluple (a,b) = (b,a)

-- | Evaluation State. Holds the Prototype Spec, the Prototype's State, and a Context which can be read from inside the Prototype monad 
data EvalState cxt st act inp outp m 
  = EvalState {
      _entity  :: EntitySpec cxt st act inp outp m 
    , _state   :: st 
    , _context :: cxt 
  }

data ExEvalState :: Type ->  Type -> (Type -> Type) -> Type where 
  ExEvalState :: EvalState cxt st act inp outp m 
              -> ExEvalState  inp outp m 

withExEval :: forall inp outp m r  
            . ExEvalState inp outp m 
            -> (forall cxt st act. EvalState cxt st act inp outp m -> r)
            -> r 
withExEval (ExEvalState e) f = f e 

new :: forall cxt i o m 
        . MonadIO m 
       => Prototype cxt i o m 
       -> cxt 
       -> m (Entity m i o) 
new (Prototype espec) c  = liftIO (newTVarIO e') >>= \e -> pure $ Entity e 
  where 
    evalSt = initE espec c 

    e' = mkEntity_ evalSt 


initE :: EntitySpec cxt st act inp outp m 
      -> cxt 
      -> EvalState cxt st act inp outp m 
initE espec@EntitySpec {..} cxt  
  = EvalState {_entity = espec 
              ,_state = _init ()
              ,_context =  cxt}  

evalAction :: act -> EvalState cxt st act inp outp m -> EntityM cxt st act outp m (Maybe outp)
evalAction act e@EvalState {..} =  _eval _entity (Action act)

type EntityStore i o m      = Store (ExEvalState i o m) (i -> m (ExEvalState i o m, Maybe o))

-- This is quite different from Halogen (which is the basis for the foundation of all the Prototype stuff) so, quick explanation: 
-- EntityS is a TVar that holds a store comonad which spits out a *function* from the input to m (newState,Maybe output)
-- This is kind of a weird construction but because StateT isn't a comonad and we need a StateT from which we can *extract* the state at any time, 
-- it serves its purpose
newtype Entity m inp outp = Entity {entity :: TVar (Store (ExEvalState inp outp m) (inp -> m (ExEvalState inp outp m, Maybe outp)))}


mkEntity_ :: forall cxt st act inp outp m
           . Monad m =>  EvalState cxt st act inp outp m -> EntityStore inp outp m 
mkEntity_ e = store go (ExEvalState e)
  where 
    go :: ExEvalState inp outp m -> (inp -> m (ExEvalState inp outp m, Maybe outp))
    go ex@(ExEvalState es@EvalState {..}) = \i -> do  
      let (EntityM ai) = _eval _entity (Receive i)
      let  st          = foldFree (accessor es) ai
      fluple <$> ST.runStateT st ex 

-- | Given an input type for some entity and the entity, run it, returning (maybe) some output 
run :: MonadIO m => i -> Entity m i o -> m (Maybe o)
run i (Entity tv) = do
  e <- liftIO $ readTVarIO tv  -- reads the store from the tvar 
  let f = extract e -- extract the input-output transfromer from the store 
  (st,o) <- f i -- apply the i-o transformer to some input 
  let newObj = withExEval st $ \x ->  mkEntity_ x  -- recreate the store comonad thingy from the new state 
  newE <- liftIO . atomically . writeTVar tv $ newObj -- write new store thingy to tvar 
  pure o 

accessor :: forall cxt' st' act' inp' outp' m' a' 
    .  Monad m' 
    => EvalState cxt' st' act' inp' outp' m'
    -> EntityF cxt' st' act' outp' m' a'
    -> ST.StateT (ExEvalState inp' outp' m') m' a' 
accessor EvalState {..} = \case 
  State f -> case f _state of 
    (a,newState) -> do 
        ST.modify $ \_ -> ExEvalState $ EvalState {_state = newState,..}
        pure a 

  Lift ma -> lift ma

  Read f -> pure (f _context)

      


