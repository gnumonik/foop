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

{- 

• Could not deduce: (Map ENode rs2 .! l)
                    ~ ENode '(i, s, ETree rs, q)
  from the context: ((('Begin ':> 'Start (Slot i_ s_ rs' q_))
                      ':> 'Down (l ':= Slot i s rs q))
                     ~ (('Begin ':> 'Start (Slot i1 su rs1 q1))
                        ':> 'Down (l' ':= Slot i' su' rs'1 q')),
                     KnownSymbol l', HasType l' (Slot i' su' rs'1 q') rs1,
                     Locate ('Begin ':> 'Start (Slot i1 su rs1 q1)),
                     Locate
                       (('Begin ':> 'Start (Slot i1 su rs1 q1))
                        ':> 'Down (l' ':= Slot i' su' rs'1 q')))
    bound by a pattern with constructor:
               ChildA' :: forall k1 k2 k3 k4 (l :: k1) (l' :: Symbol) i su
                                 (rs :: Row SlotData) (ss :: k2) (q :: Type -> Type) i' su'
                                 (rs' :: Row SlotData) (ss' :: k3) (q' :: Type -> Type) (old :: k4).
                          (KnownSymbol l', HasType l' (Slot i' su' rs' q') rs,
                           Locate ('Begin ':> 'Start (Slot i su rs q)),
                           Locate
                             (('Begin ':> 'Start (Slot i su rs q))
                              ':> 'Down (l' ':= Slot i' su' rs' q'))) =>
                          SlotKey l' rs (Slot i' su' rs' q')
                          -> Segment' ('Begin ':> 'Start (Slot i su rs q))
                          -> Segment'
                               (('Begin ':> 'Start (Slot i su rs q))
                                ':> 'Down (l' ':= Slot i' su' rs' q')),
             in an equation for ‘locate’
    at /home/gsh/code/haskell/foop/src/Data/Foop/Paths.hs:44:11-33
  or from: HasType l (ENode (Slot i s rs q)) (Map ENode rs')
    bound by a type expected by the context:
               HasType l (ENode (Slot i s rs q)) (Map ENode rs') =>
               STM (ENode '(i, s, ETree rs, q))
    at /home/gsh/code/haskell/foop/src/Data/Foop/Paths.hs:45:68-95
• In the second argument of ‘($)’, namely ‘roots .! (Label @l)’
  In the second argument of ‘($)’, namely
    ‘pure $ roots .! (Label @l)’
  In the expression:
    withDict (deriveHas @ENode key) $ pure $ roots .! (Label @l)
• Relevant bindings include
    roots :: Rec (Map ENode rs2)
      (bound at /home/gsh/code/haskell/foop/src/Data/Foop/Paths.hs:45:21)
    e :: Entity
           (Source
              (('Begin ':> 'Start (Slot i_ s_ rs' q_))
               ':> 'Down (l ':= Slot i s rs q)))
      (bound at /home/gsh/code/haskell/foop/src/Data/Foop/Paths.hs:44:36)
    locate :: Segment'
                (('Begin ':> 'Start (Slot i_ s_ rs' q_))
                 ':> 'Down (l ':= Slot i s rs q))
              -> Entity
                   (Source
                      (('Begin ':> 'Start (Slot i_ s_ rs' q_))
                       ':> 'Down (l ':= Slot i s rs q)))
              -> STM
                   (ENode
                      (Target
                         (('Begin ':> 'Start (Slot i_ s_ rs' q_))
                          ':> 'Down (l ':= Slot i s rs q))))
      (bound at /home/gsh/code/haskell/foop/src/Data/Foop/Paths.hs:44:3)

-}

popRoots :: Entity (Slot i su rs q) -> STM (ETree rs) 
popRoots (Entity e) = readTVar e >>= \t-> case pos t of 
  ExEvalState (EvalState _ _ _ roots _ _) -> pure roots 

instance Locate ('Begin ':> 'Start (Slot i s rs q)) where 
  locate Here' e = pure $ mkENode e 

instance (rs .! l) ~ (Slot i' s' rs' q') =>  Locate ('Begin :> 'Start ( Slot i s rs q) :> 'Down (l ':= Slot i' s' rs' q')) where 
  locate (ChildA' key@SlotKey old) e = locate old e >>= \case 
    en@(ENode e'  :: ENode (Slot i s rs q)) -> case deriveHas @ENode key of 
      d@Dict -> go d en 
   where 
      go :: Dict (HasType l (ENode (Slot i' s' rs' q')) (Map ENode rs))
         -> ENode (Slot i s rs q) 
         -> STM (ENode (Slot i' s' rs' q'))
      go d (ENode e' ) = popRoots e' >>= \case 
        ETree roots' -> withDict d $ pure $ roots' R..! (Label @l)


instance Locate (old :> 'Down  (_l ':= Slot i_ s_ rs' q_)) 
      => Locate (old :> 'Down  (_l ':= Slot i_ s_ rs' q_)  :> 'Down (l ':= Slot i s rs q)) where 
  locate (ChildB' key@SlotKey old) e = locate old e >>= \case 
    (ENode e') -> popRoots e' >>= \case 
      ETree roots' -> withDict (deriveHas @ENode key) $ pure $ roots' R..! (Label @l)

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



{--
class ( Forall (Project source) NormalCharted
      , Forall (Project source) Locate 
      , AllUniqueLabels (R.Map Proxy (Project source))
      , AllUniqueLabels (Project source)
      , KnownSymbol (L lt) 
    --  , HasType (L lt) _hm (Project source)
    --  , Fo 
      , Forall (R.Map Proxy (Project source)) Default) => HasPathAt (source :: SlotData) (lt :: Symbol := SlotData) where 
  pathify :: forall l slot (xs :: Path)
           . ( lt ~ (l ':= slot)
             , KnownSymbol l
             , HasType l (xs :> 'Down (l ':= slot)) (Project source)
             , (Project source .! l) ~ (xs :> 'Down (l ':= slot)) 
             , Source xs ~ source 
             , Target (Project source .! l) ~ slot 
             ) => TMVar (Entity source)
               -> STMNode slot 
  pathify tmv = STMNode $ readTMVar tmv >>= \e ->  locate' myPath e 
    where  
      proxified  = mkProxy (Proxy @(Project source))

      myPath :: Segment' (xs :> 'Down (l ':= slot))
      myPath = withDict (mapHas @Segment' @l @(xs :> 'Down (l ':= slot)) @(Project source)) $ pathed R..! (Label @l)

      pathed :: Rec (R.Map Segment' (Project source))
      pathed = R.transform @NormalCharted @(Project source) @Proxy @Segment' go proxified 

      go :: forall p. (Charted p, Normalized p) => Proxy p -> Segment' p 
      go Proxy = chart @p
 --}

{--
instance ( Forall (Project source) NormalChartedLocate 
      , Forall (Project source) Locate 
      , AllUniqueLabels (R.Map Proxy (Project source))
      , AllUniqueLabels (Project source)
      , Forall (R.Map Proxy (Project source)) Default) => HasPathAt (source :: SlotData) (lt :: Symbol := SlotData)
--}