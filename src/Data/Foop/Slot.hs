{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Data.Foop.Slot where


import Data.Foop.Types
import Data.Row
    ( (.!),
      type (.+),
      type (.==),
      AllUniqueLabels,
      Empty,
      Forall,
      Label(Label),
      Row,
      Rec )
import qualified Data.Row.Records as R
import qualified Data.Map as M
import Data.Proxy ( Proxy(..) )
import Data.Default ( Default(..) )
import Control.Concurrent.STM ( readTVar, STM, atomically )
import Data.Constraint ( withDict )
import Data.Foop.Dictionary 
import Control.Comonad.Store ( ComonadStore(pos) )
import Data.Row.Internal
    ( type (.+),
      type (.==),
      AllUniqueLabels,
      Empty,
      Forall,
      Label(Label),
      Row(..), 
      LT(..) )
import GHC.TypeLits (Symbol, TypeError, KnownSymbol)
import Data.Row.Dictionaries (mapHas, Unconstrained1)
import Data.Foop.Exists 

-- | Given an Entity, renders its surface. Doesn't run the IO action.


-- passing around SlotKeys b/c writing all these constraints everywhere gets tiring 
lookupLeaf :: forall label slots slot
               . KnownSymbol label 
              => ShootKey label slots slot
              -> EBranch slots 
              -> ELeaf slot
lookupLeaf (key@(ShootKey )) (EBranch storage) = withDict (deriveHas' @ELeaf @label @slots @slot) $ storage .! (Label @label)


{--
modifyStorage :: forall label slots slot
               . SlotKey label slots slot
              -> (EBranch slot -> EBranch slot)
              -> Rec (R.Map EBranch slots)
              -> Rec (R.Map EBranch slots)
modifyStorage key@SlotKey f storage
  = withDict (deriveHas @EBranch key)
  $ R.update (Label @label) (f $ storage .! (Label @label)) storage
--}


type TestRow = "slot1" .== Slot String Empty Empty Maybe
            .+ "slot2" .== Slot Int Empty Empty Maybe

instance Default (Proxy (a :: k)) where
  def = Proxy

apSegment :: forall slot path x. slot ~ Source path => Segment x path -> Segment x path 
apSegment = id 


{--
mkRenderTree :: ( AllUniqueLabels slots
                , AllUniqueLabels (R.Map Proxy slots)
                , Forall slots SlotOrdC
                , Forall (R.Map Proxy slots) Default
                , R.Map RenderBranch slots1 ~ R.Map RenderBranch slots2
                ) => Proxy slots 
                  -> IO (RenderTree slots)
mkRenderTree proxy = MkRenderTree <$> atomically (toSurface proxy (mkStorage proxy))
--}

toStorage :: forall slots.  (Forall slots SlotOrd) => 
             Proxy slots
          -> Rec (R.Map Proxy slots)
          -> EBranch slots
toStorage proxy xs = EBranch $ R.transform @SlotOrd  @slots @Proxy @ELeaf go xs 
  where
    go :: forall slot 
        . SlotOrd slot 
       => Proxy slot
       -> ELeaf slot
    go proxy' = emptyLeaf 


mkStorage proxy = toStorage proxy $ mkProxy  proxy

projProxy :: Proxy (slot :: SlotData) -> Proxy (Project slot)
projProxy Proxy = Proxy 

hmwmbm = projProxy (Proxy @MySlot)

type MySlot = Slot Bool Row1 Empty Maybe 

type Row1 :: Row SlotData 
type Row1 = "rootSlotA" .== Slot  Int Empty Empty (Either String)
         .+ "rootSlotB" .== Slot  Int Row2  Empty Maybe 

type Row2 :: Row SlotData 
type Row2 = "depth1SlotA" .== Slot  Double Empty Empty Maybe 
         .+ "depth1SlotB" .== Slot  String Row3  Empty (Either Bool)

type Row3 :: Row SlotData 
type Row3 = "depth2SlotA" .== Slot () Empty Empty []
 

