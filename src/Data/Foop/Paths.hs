{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
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


newtype STMNode :: SlotData -> Type where 
  STMNode :: STM (ENode slot) -> STMNode slot    


class (Charted p, Normalized p, SourceOf p source, TargetOf p target) => ConcretePath source target p where 
  concretePath :: Dict (Charted p, Normalized p, SourceOf p source, TargetOf p target)
  concretePath = Dict 

instance (Charted p, Normalized p, SourceOf p source, TargetOf p target) => ConcretePath source target p

type family L (lt :: LT SlotData) :: Symbol where 
  L (l ':-> t) = l

type family T (lt :: LT SlotData) :: SlotData where 
  T (l ':-> t) = t
 

data HasSome' :: (k -> Constraint) -> Symbol -> Row k -> Type where 
  HasSome :: forall k (c :: k -> Constraint) (rk :: Row k) (l :: Symbol) 
          . ( WellBehaved rk 
            , KnownSymbol l 
            , HasType l (rk .! l) rk 
            , c (rk .! l)) => HasSome' c l rk 

data Some :: (k -> Constraint) -> (k -> Type) -> Type where 
  Some :: forall k (c :: k -> Constraint) (f :: k -> Type) (a :: k)
        . c a => f a -> Some c f 





unSome :: Some c f -> (forall a. c a => f a -> r) -> r 
unSome (Some a) f = f a 
   
            
withSome :: forall k (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) r. HasSome c l rk => (forall (x :: k). c x => r) -> r 
withSome f = case (hasSome :: HasSome' c l rk) of 
  HasSome -> f @(rk .! l)

withSome' :: forall k (c :: k -> Constraint) (l :: Symbol) (rk :: Row k) r. HasSome' c l rk -> (forall (x :: k). c x => r) -> r 
withSome' h f = case h of 
  HasSome -> f @(rk .! l)

class HasSome (c :: k -> Constraint) (l :: Symbol) (rk :: Row k)  where 
  hasSome :: HasSome' c l rk 

instance ( HasType l (rk .! l) rk
         , c (rk .! l) 
         , WellBehaved rk 
         , KnownSymbol l ) =>  HasSome c l rk   where 
           hasSome = HasSome

class Source path ~ slot => SourceOf path slot where 
  sourceOf :: Dict (Source path ~ slot)
  sourceOf = Dict 

class Target path ~ slot => TargetOf path slot where 
  targetOf :: Dict (Target path ~ slot)
  targetOf = Dict 

instance Source path ~ slot => SourceOf path slot 

instance Target path ~ slot => TargetOf path slot 

targetOf' :: TargetOf path slot :- (Target path ~ slot)
targetOf' = Sub Dict 

getSome :: forall k (f :: k -> Type) l (c :: k -> Constraint)  (rk :: Row k) 
         . KnownSymbol l
        => HasSome' c l rk 
        -> (forall (a :: k). c a =>  f a) 
        -> Some c f 
getSome HasSome f = Some $ f @(rk .! l)

data ProxE :: forall k. k -> Type where 
  ProxE :: forall k (a :: k). Top a => ProxE a 

proxE :: forall k (a :: k). ProxE a 
proxE = ProxE  

newtype TopDict a = TopDict (Dict (Top a))

class (HasSome (ConcretePath source slot) l (Project source)
      , KnownSymbol l 
      , WellBehaved (Project source)) => Compatible source slot l where 
  unify :: TMVar (Entity source) -> STMNode slot 
  unify tmv = STMNode $ readTMVar tmv >>= \e -> 
    case hasSome :: HasSome' (ConcretePath source slot) l (Project source) of 
      h@HasSome -> case  (getSome  h proxE :: Some (ConcretePath source slot) ProxE) of 
        x -> go x e 
   where 
     go ::  Some (ConcretePath source slot) ProxE -> Entity source -> STM (ENode slot)
     go x e = unSome x (go2 e)

     go2 :: forall (a :: Path) (slot :: SlotData) (source :: SlotData)
          . ConcretePath source slot a =>  Entity source -> ProxE a -> STM (ENode slot)
     go2 e ProxE = locate' @a (chart @a) e 

instance (HasSome (ConcretePath source slot) l (Project source)
      , KnownSymbol l 
      , WellBehaved (Project source)) => Compatible source slot l

class (Compatible source (T lt) (L lt), KnownSymbol (L lt)) => Compatible' source (lt :: LT SlotData) where 
  unify' :: TMVar (Entity source) -> STMNode (T lt)
  unify' e = unify @source @(T lt) @(L lt) e

instance (Compatible source (T lt) (L lt), KnownSymbol (L lt)) => Compatible' source (lt :: LT SlotData) 

class HasType l (l ':-> k) rk => HasLTK l k rk 

type Labelled :: Row k -> Row (LT k)
type family Labelled rk = lt | lt -> rk where 
  Labelled (R lts) = R (LabelledR lts) 

type LabelledR :: [LT k] -> [LT (LT k)]
type family LabelledR rk = lt | lt -> rk  where 
  LabelledR '[] = '[]
  LabelledR (l ':-> k ': lts) = (l ':-> (l ':-> k)) ': LabelledR lts 


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