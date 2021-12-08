{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE RecordWildCards #-}
module Data.Foop.Paths where


import Data.Foop.Types
import qualified Data.Map as M
import Data.Row.Dictionaries
import Data.Row
import Data.Row.Internal
import qualified Data.Row.Records as R
import Control.Concurrent.STM
import Data.Kind
import Control.Comonad.Store
import Control.Concurrent.STM 
import Control.Monad
import Data.Foop.Slot 
import Data.Foop.Exists
import Data.Foop.Dictionary 
import GHC.Base
import Data.Proxy
import Data.Default
import Data.Constraint 
import Unsafe.Coerce

data RootOf :: Path -> Type where 
  RootOf :: forall root parent  
          . root ~ Source parent 
         => TMVar (Entity root) 
         -> RootOf parent

mkENode :: Entity slot -> ENode slot 
mkENode = undefined 

popRoots :: Entity (Slot su rs ds q) -> STM (ETree rs) 
popRoots (Entity e) = readTVar e >>= \t-> case pos t of 
  ExEvalState (EvalState _ _ roots _ _ _) -> pure roots 

instance Locate ('Begin ':> 'Start (Slot  s rs ds q)) where 
  locate Here' e = pure $ mkENode e 

instance (rs .! l) ~ (Slot s' rs' ds' q') =>  Locate ('Begin :> 'Start ( Slot s rs ds q) :> 'Down (l ':= Slot s' rs' ds' q')) where 
  locate (ChildA' key@SlotKey old) e = locate old e >>= \case 
    en@(ENode e'  :: ENode (Slot s rs ds q)) -> case deriveHas @ENode key of 
      d@Dict -> go d en 
   where 
      go :: Dict (HasType l (ENode (Slot s' rs' ds' q')) (Map ENode rs))
         -> ENode (Slot s rs ds q) 
         -> STM (ENode (Slot s' rs' ds' q'))
      go d (ENode e' ) = popRoots e' >>= \case 
        ETree roots' -> withDict d $ pure $ roots' R..! (Label @l)

{-
instance Locate (old :> 'Down  (_l ':= Slot s_ rs' ds' q_)) 
      => Locate (old :> 'Down  (_l ':= Slot s_ rs' ds' q_)  :> 'Down (l ':= Slot s rs ds q)) where 
  locate (ChildB' key@SlotKey old) e = locate old e >>= \case 
    (ENode e') -> popRoots e' >>= \case 
      ETree roots' -> withDict (deriveHas @ENode key) $ pure $ roots' R..! (Label @l)


data AnAtlasOf :: Row Type -> Type where 
  AnAtlasOf :: Forall children (Exists (Extends parent) (Segment 'Begin)) 
            => Atlas parent children 
            -> AnAtlasOf children 

data Atlas :: Path -> Row Type -> Type where 
  MkAtlas :: forall parent children 
           . TMVar (Entity (Source parent))
          -> Unified parent children 
          -> Atlas parent children

data Navigator :: Path -> Path -> Type where 
  MkNavigator :: forall source destination 
              . (Entity (Source source) -> STM (ENode (Target destination)))
              -> Navigator source destination

type Unified parent children 
  = Rec (R.Map (Deriving (Extends parent) (Segment 'Begin) (Navigator parent)) children)


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

class Forall children (Exists (Extends parent) (Segment 'Begin))  
    => AllExtend parent children where 
      atlas :: RootOf parent
            -> Segment 'Begin parent 
            -> Rec children 
            -> AnAtlasOf children
      atlas = mkAnAtlasOf 

instance Forall children (Exists (Extends parent) (Segment 'Begin))  
    => AllExtend parent children 

mkAtlas :: forall parent children   
         . ( Forall children (Exists (Extends parent) (Segment 'Begin))) 
        => RootOf parent
        -> Segment 'Begin parent 
        -> Rec children 
        -> Atlas parent children 
mkAtlas (RootOf tmv) parentPath children = case unifyPaths parentPath children of 
  unified -> go tmv unified 
 where 
   go :: forall root
       . root ~ Source parent 
      => TMVar (Entity root) 
      -> Unified parent children 
      -> Atlas parent children 
   go t u = MkAtlas t u 

mkAnAtlasOf :: Forall children (Exists (Extends parent) (Segment 'Begin)) 
            => RootOf parent 
            -> Segment 'Begin parent 
            -> Rec children 
            -> AnAtlasOf children
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
-}