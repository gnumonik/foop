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
import Data.Foop.Slot 
import Data.Foop.Exists
import Data.Foop.Dictionary 
import GHC.Base
import Data.Proxy
import Data.Default



data RootOf :: Path -> Type where 
  RootOf :: forall root parent  
          . root ~ Source parent 
         => TMVar (Entity root) 
         -> RootOf parent

mkENode :: Entity slot -> ENode slot 
mkENode = undefined 

instance Locate ('Begin ':> 'Start (Slot i s rs q)) where 
  locate Here' e = pure $ mkENode e 

instance Locate ('Begin :> 'Start ( Slot i_ s_ rs' q_) :> 'Down (l ':= Slot i s rs q)) where 
  locate (ChildA' key@SlotKey old) e = locate old e >>= \case 
    (ENode _ (ETree roots) _) -> withDict (deriveHas @ENode key) $ pure $ roots R..! (Label @l)

instance Locate (old :> 'Down  (_l ':= Slot i_ s_ rs' q_)) 
      => Locate (old :> 'Down  (_l ':= Slot i_ s_ rs' q_)  :> 'Down (l ':= Slot i s rs q)) where 
  locate (ChildB' key@SlotKey old) e = locate old e >>= \case 
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

data PathFromTo :: SlotData -> SlotData -> Type where 
  PathFromTo :: forall path slot source 
                . ( Target path ~ slot 
                  , Source path ~ source ) 
               => Segment' path ->  PathFromTo source slot  

newtype STMNode :: SlotData -> Type where 
  STMNode :: STM (ENode slot) -> STMNode slot    

class (Charted p, Normalized p, Locate p) => NormalChartedLocate p where 
  normalCharted :: Dict (Charted p, Normalized p)
  normalCharted = Dict 

instance (Charted p, Normalized p, Locate p) => NormalChartedLocate p 

type family L (lt :: Symbol := SlotData) :: Symbol where 
  L (l ':= t) = l

type family T (lt :: Symbol := SlotData) :: SlotData where 
  T (l ':= t) = t
 

data HasCAt :: (k -> Constraint) -> Symbol -> Row k -> Type -> Type where 
  HasCAt :: forall k (c :: k -> Constraint) (rk :: Row k) (l :: Symbol) t
          . ( WellBehaved rk 
            , KnownSymbol l 
            , HasType l (rk .! l) rk 
            , c (rk .! l)
            , Proxy (rk .! l) ~ t) => HasCAt c l rk t 

class HasCAtC (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) t where 
  hasCAt :: HasCAt c l rk t 

instance ( HasType l (rk .! l) rk
         , c (rk .! l) 
         , WellBehaved rk 
         , KnownSymbol l 
         , t ~ Proxy (rk .! l)) =>  HasCAtC c l rk t  where 
           hasCAt = HasCAt 

type ARow = "pewps" .== Int 
         .+ "scewps" .== (Int -> Bool)

testHas :: forall c l rk t. HasCAtC c l rk t => Proxy t 
testHas = Proxy 



class ( Forall (Project source) NormalChartedLocate 
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
             , ((Project source) .! l) ~ (xs :> 'Down (l ':= slot)) 
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
      pathed = R.transform @NormalChartedLocate @(Project source) @Proxy @Segment' go proxified 

      go :: forall p. (Charted p, Normalized p) => Proxy p -> Segment' p 
      go Proxy = chart @p


{--
instance ( Forall (Project source) NormalChartedLocate 
      , Forall (Project source) Locate 
      , AllUniqueLabels (R.Map Proxy (Project source))
      , AllUniqueLabels (Project source)
      , Forall (R.Map Proxy (Project source)) Default) => HasPathAt (source :: SlotData) (lt :: Symbol := SlotData)
--}