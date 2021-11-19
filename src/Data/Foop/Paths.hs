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

data AnAtlasOf :: Row Type -> Type where 
  AnAtlasOf :: Forall children (Exists (ExtendPath parent) (PathFinder 'Begin)) 
            => Atlas parent children 
            -> AnAtlasOf children 


instance Locate root (old :> 'Down_ slots) => Locate root ((old :> 'Down_ slots) :> 'Branch_ (l ':= Slot i su cs q)) where 
  locate (Branch' key@SlotKey old) e = locate old e >>= \case 
    Nothing -> pure Nothing
    Just (MkStorageTree b) -> pure . Just $ lookupStorage key b 

instance  Locate (Slot i su cs q) ('Begin :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
  locate (Down' Start') (Entity e) = (pos <$> readTVar e) >>= \case
    ExEvalState (EvalState _ _ storage _ _ _) -> pure . Just $ MkStorageTree storage 

instance Locate root (old :> 'Branch_ (l ':= Slot i su cs q)) => Locate root (old :> 'Branch_ (l ':= Slot i su cs q) :> 'Leaf_ (Slot i su cs q)) where 
  locate (Leaf' i old) e = locate old e >>= \case 
    Nothing -> pure Nothing 
    Just (MkStorageBox storage) -> pure $ M.lookup (Indexed Index i) storage 

instance Locate root (old1 :> 'Leaf_ (Slot i su cs q)) => Locate root (old1 :> 'Leaf_ (Slot i su cs q) :> 'Down_ cs) where 
  locate (Down' old) e = locate old e >>= \case 
    Nothing -> pure Nothing 
    Just (Entity e) -> readTVar e >>= \e' -> case pos e' of 
      ExEvalState (EvalState _ _ storage _ _ _) -> pure . Just $ MkStorageTree storage 

mkPointed :: forall parent child
           . ( ExtendPath parent child )  
          => PathFinder 'Begin parent 
          -> PathFinder 'Begin child 
          -> Pointed parent child 
mkPointed parent child = MkPointed $ readTMVar >=> locate (normalizePF $ extendPath parent child) 

allHave :: forall f c children 
        . AllHave f c children
       => Rec children 
       -> Rec (R.Map (Ex c f) children)
allHave = R.map @(Exists c f) go 
  where 
    go :: forall t 
        . Exists c f t 
       => t 
       -> Ex c f t 
    go t = case exW :: ExW c f t of 
      h@ExW -> Ex t 

allTransform :: forall c f g h children 
              . Forall children Unconstrained1 
             => Rec (R.Map (Deriving c f g) children)
             -> (forall x. c x => g x -> h x) 
             -> Rec (R.Map (Deriving c f h) children)
allTransform old f = R.transform' @children @(Deriving c f g) @(Deriving c f h) go old 
  where 
    go :: forall t. Deriving c f g t -> Deriving c f h t
    go mx = mx -/-> f 

allTo :: forall f g c children 
       .  Forall children (Exists c f) 
      => (forall a. c a => f a -> g a ) 
      -> Rec (R.Map (Ex c f ) children)
      -> Rec (R.Map (Deriving c f g) children)
allTo f = R.transform @(Exists c f) @children @(Ex c f) @(Deriving c f g) go 
  where 
    go :: forall t. Exists c f t => Ex c f t -> Deriving c f g t 
    go (Ex ft) = Deriving f (Ex ft)

unifyPaths :: forall parent children 
            . ( Forall children (Exists (ExtendPath parent) (PathFinder 'Begin)) )
           => PathFinder 'Begin parent 
           -> Rec children 
           -> Rec (R.Map (Deriving (ExtendPath parent) (PathFinder 'Begin) (Pointed parent)) children)
unifyPaths pt rs = b
  where 
    a :: Rec (R.Map (Ex (ExtendPath parent) (PathFinder 'Begin)) children)
    a = allHave 
          @(PathFinder 'Begin) 
          @(ExtendPath parent)  
          rs 

    b :: Rec (R.Map (Deriving (ExtendPath parent) (PathFinder 'Begin) (Pointed parent)) children)
    b = allTo 
          @(PathFinder 'Begin) 
          @(Pointed parent) 
          @(ExtendPath parent) 
          @children 
          (mkPointed pt) a 

mkAtlas :: forall parent children root  
         . ( Forall children (Exists (ExtendPath parent) (PathFinder 'Begin))) 
        => Root parent 
        -> PathFinder 'Begin parent 
        -> Rec children 
        -> Atlas parent children 
mkAtlas (MkRoot tmv) parentPath children = case unifyPaths parentPath children of 
  unified -> go tmv unified 
 where 
   go :: forall root
       . root ~ RootOf parent 
      => TMVar (Entity root) 
      -> Unified parent children 
      -> Atlas parent children 
   go t u = MkAtlas t u 

mkAnAtlasOf :: Forall children (Exists (ExtendPath parent) (PathFinder 'Begin)) 
            => Root parent
            -> PathFinder 'Begin parent -> Rec children -> AnAtlasOf children
mkAnAtlasOf root parent children = AnAtlasOf $ mkAtlas root parent children 


withAtlas :: forall l children path
           . ( HasType l (PathFinder 'Begin path) children
           , AllUniqueLabels children 
           , KnownSymbol l
           ) => AnAtlasOf children
             -> STM (Maybe (TraceE path))
withAtlas (AnAtlasOf atlas@(MkAtlas _ _)) = goA atlas 
  where 
    goA :: forall parent
        . Atlas parent children
       -> STM (Maybe (TraceE path))
    goA (MkAtlas tmv unified) = readTMVar tmv >>= \e ->  goB e unified 
      where 
        goB :: Entity (LeafMe (First parent))
            -> Rec (R.Map (Deriving  (ExtendPath parent) (PathFinder 'Begin) (Pointed parent)) children)
            -> STM (Maybe (TraceE path))
        goB (Entity e) unified' -- logic time  
          = withDict myDict 
            $ case unified R..! (Label @l) of 
                (mx@(Deriving f (Ex ft)) :: (Deriving  (ExtendPath parent) (PathFinder 'Begin) (Pointed parent)) (PathFinder 'Begin path))
                  -> discharge mx $ \(MkPointed g) -> g tmv
         where 
          myDict = mapHas @(Deriving  (ExtendPath parent) (PathFinder 'Begin) (Pointed parent))
                             @l 
                             @(PathFinder 'Begin path)
                             @children
