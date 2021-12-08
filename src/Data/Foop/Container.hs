module Data.Foop.Container where 


import Data.Foop
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad ( replicateM_ ) 
import Data.Functor ((<&>))
import Control.Monad.State.Class ( MonadState(get), modify' ) 
import Data.Row ( Empty, type (.==), type (.+), (.==), (.+) ) 
import Data.Proxy (Proxy (Proxy)) 
import Control.Concurrent.STM () 
import Data.Row.Internal
import Data.Default
import qualified Data.Constraint.Forall as DC  
import Data.Constraint
import Data.Foop.Slot
import qualified Data.Row.Records as R
import Data.Kind
import Data.Foop.Exists
import Data.Functor.Constant
import Data.Void
import qualified Data.Map as M
import Control.Concurrent.STM 
import Control.Monad.State
import Control.Monad.Free.Church

type SlotI i su cs ds q = IxSlot i (Slot su cs ds q)

origin :: forall deps roots state query r 
       . (forall su. Origin (Slot su roots deps query) -> r) 
      -> EntityM deps roots state query IO r
origin f = EntityM . liftF $ Origin f 

data ContainerLogic :: Type -> SlotData -> Type -> Type where 
  Tell :: forall i su rs ds q x
        . Ord i
       => i  
       -> q ()
       -> x 
       -> ContainerLogic i (Slot su rs ds q) x 

  Request :: forall i su rs ds q a x   
           . Ord i
          => i 
          -> q a
          -> (Maybe a -> x)
          -> ContainerLogic i (Slot su rs ds q) x 

  Create :: forall i su rs ds q source x  
          . ( Ord i 
          ,   Coherent source (Slot su rs ds q))
          => i 
          -> Model (Slot su rs ds q)
          -> TMVar (Entity source) 
          -> x  
          -> ContainerLogic i (Slot su rs ds q) x 

  Delete :: forall i su rs ds q x   
          . Ord i  
         => i 
         -> x 
         -> ContainerLogic i (Slot su rs ds q) x 


mkContainer :: forall i su rs ds q    
              . Ord i 
             => Model (Slot su rs ds q)
             -> Model ( Slot (M.Map i (Entity (Slot su rs ds q))) 
                        rs 
                        ds 
                        (ContainerLogic i (Slot su rs ds q)))
mkContainer (Model (MkSpec iSt b rndr ds) mdls ) = flip Model mdls $ MkSpec {
    initialState = M.empty 
  , handleQuery  = mkQHandler ds $ runContainerLogic 
  , renderer     = MkRenderer id (pure . const ())
  , atlas        = ds
  } where 
      runContainerLogic :: forall x
                         . Chart ds rs
                        -> ContainerLogic i (Slot su rs ds q) x
                        -> EntityM ds rs (M.Map i (Entity (Slot su rs ds q))) (ContainerLogic i (Slot su rs ds q)) IO x
      runContainerLogic _ = \case 
        Tell i q x -> gets (M.lookup i) >>= \case 
          Nothing -> pure x
          Just e  -> liftIO (run q e) >> pure x 

        Request i q f -> gets (M.lookup i) >>= \case 
          Nothing -> pure $ f Nothing
          Just e  -> f . Just <$> liftIO (run q e) 

        Create i mo tmv x -> origin  (goCreate i mo) >> pure x 

        Delete i x -> modify' (M.delete i) >> pure x 
       where 
         goCreate :: forall sx 
                   . i
                  -> Model (Slot su rs ds q)
                  -> Origin (Slot su rs ds (ContainerLogic i (Slot su rs ds q)))
                  -> EntityM ds rs (M.Map i (Entity (Slot su rs ds q))) (ContainerLogic i (Slot su rs ds q)) IO () 
         goCreate i mdl org@(MkOrigin tmv) =  unOrigin org (go mdl) 
           where 
             go :: forall source
                 . Model (Slot su rs ds q) 
                -> Dict (Coherent source (Slot su rs ds q))
                -> TMVar (Entity source)
                -> EntityM
                    ds
                    rs
                    (M.Map i (Entity (Slot su rs ds q)))
                    (ContainerLogic i (Slot su rs ds q))
                    IO
                    ()
             go = undefined 
             
