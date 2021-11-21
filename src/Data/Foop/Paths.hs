{-# LANGUAGE ConstraintKinds #-}
module Data.Foop.Paths where


import Data.Foop.Types
import qualified Data.Map as M
import Data.Row.Dictionaries
import Data.Row
import qualified Data.Row.Records as R
import Control.Concurrent.STM
import Data.Kind
import Control.Comonad.Store
import Control.Concurrent.STM 
import Control.Monad
import Data.Foop.Slot (lookupStorage)
import Data.Foop.Exists
import Data.Foop.Dictionary 


mkENode :: Entity slot -> ENode slot 
mkENode = undefined 

instance Locate ('Begin ':> 'Start (l ':= Slot i s rs q)) where 
  locate Here' e = pure $ mkENode e 

instance Locate ('Begin :> 'Start (_l ':= Slot i_ s_ rs' q_) :> 'Down (l ':= Slot i s rs q)) where 
  locate (Child' key@SlotKey old) e = locate old e >>= \case 
    (ENode _ (ETree roots) _) -> withDict (deriveHas @ENode key) $ pure $ roots R..! (Label @l)

instance Locate (old :> 'Down  (_l ':= Slot i_ s_ rs' q_)) 
      => Locate (old :> 'Down  (_l ':= Slot i_ s_ rs' q_)  :> 'Down (l ':= Slot i s rs q)) where 
  locate (Child' key@SlotKey old) e = locate old e >>= \case 
    (ENode _ (ETree roots) _) -> withDict (deriveHas @ENode key) $ pure $ roots R..! (Label @l)

mkNavigator :: forall source destination 
             . Extends source destination 
            => Segment 'Begin source 
            -> Segment 'Begin destination 
            -> Navigator source destination 
mkNavigator src dst = MkNavigator $ \e ->  locate (extendPath src dst) e

unifyPaths :: forall parent children 
            . ( Forall children (Exists (Extends parent) (Segment 'Begin)) )
           => Segment 'Begin parent 
           -> Rec children 
           -> Rec (R.Map (Deriving (Extends parent) (Segment 'Begin) (Navigator parent)) children)
unifyPaths pt rs = b
  where 
    a :: Rec (R.Map (Ex (Extends parent) (Segment 'Begin)) children)
    a = allHave 
          @(Segment 'Begin) 
          @(Extends parent)  
          rs 

    b :: Rec (R.Map (Deriving (Extends parent) (Segment 'Begin) (Navigator parent)) children)
    b = allTo 
          @(Segment 'Begin) 
          @(Navigator parent) 
          @(Extends parent) 
          @children 
          (mkNavigator pt) a 

mkAtlas :: forall parent children root  
         . ( Forall children (Exists (Extends parent) (Segment 'Begin))) 
        => TMVar (Entity (Source parent))
        -> Segment 'Begin parent 
        -> Rec children 
        -> Atlas parent children 
mkAtlas tmv parentPath children = case unifyPaths parentPath children of 
  unified -> go tmv unified 
 where 
   go :: forall root
       . root ~ Source parent 
      => TMVar (Entity root) 
      -> Unified parent children 
      -> Atlas parent children 
   go t u = MkAtlas t u 

mkAnAtlasOf :: Forall children (Exists (Extends parent) (Segment 'Begin)) 
            => TMVar (Entity (Source parent)) 
            -> Segment 'Begin parent -> Rec children -> AnAtlasOf children
mkAnAtlasOf root parent children = AnAtlasOf $ mkAtlas root parent children 

withAtlas :: forall l children path
           . ( HasType l (Segment 'Begin path) children
           , AllUniqueLabels children 
           , KnownSymbol l
           ) => AnAtlasOf children
             -> STM (ENode (Target path))
withAtlas (AnAtlasOf atlas@(MkAtlas _ _)) = goA atlas 
  where 
    goA :: forall parent
        . Atlas parent children
       -> STM (ENode (Target path))
    goA (MkAtlas tmv unified) = readTMVar tmv >>= \e ->  goB e unified 
      where  
        goB :: Entity (Source parent)
            -> Rec (R.Map (Deriving  (Extends parent) (Segment 'Begin) (Navigator parent)) children)
            -> STM (ENode (Target path))
        goB e unified' -- logic time  
          = withDict myDict 
            $ case unified R..! (Label @l) of 
                (mx@(Deriving f (Ex ft)) :: (Deriving  (Extends parent) (Segment 'Begin) (Navigator parent)) (Segment 'Begin path))
                  -> discharge mx $ \(MkNavigator g) -> g e
         where 
          myDict = mapHas @(Deriving  (Extends parent) (Segment 'Begin) (Navigator parent))
                             @l 
                             @(Segment 'Begin path)
                             @children

