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
import Data.Row.Dictionaries (mapHas)
import Data.Foop.Exists 

-- | Given an Entity, renders its surface. Doesn't run the IO action.
{--
observeE :: forall slot
         .  Entity slot
         -> STM (RenderLeaf slot)
observeE (Entity tv) =  do
  e <- readTVar tv
  case pos e of -- can't use let, something something monomorphism restriction 
    ExEvalState EvalState{..} -> do
      let surface = render (renderer  _entity)  _state
      children <- toSurface (slots _entity) _storage
      pure $ MkRenderLeaf surface (MkRenderTree children)
--}
-- passing around SlotKeys b/c writing all these constraints everywhere gets tiring 
lookupLeaf :: forall label slots slot
               . KnownSymbol label 
              => SlotKey label slots slot
              -> EBranch slots 
              -> ELeaf slot
lookupLeaf key@SlotKey (EBranch storage) = withDict (deriveHas @ELeaf key) $ storage .! (Label @label)


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


type TestRow = "slot1" .== Slot Int String Empty Maybe
            .+ "slot2" .== Slot String Int Empty Maybe

instance Default (Proxy (a :: k)) where
  def = Proxy
{--

--}
apSegment :: forall slot path x. slot ~ Source path => Segment x path -> Segment x path 
apSegment = id 


wumbum = Here +> Parent +> Parent 



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

toStorage :: forall slots. (Forall slots (SlotI Ord))
          => Proxy slots
          -> Rec (R.Map Proxy slots)
          -> EBranch slots
toStorage proxy xs = EBranch $ R.transform @(SlotI Ord) @slots @Proxy @ELeaf go xs 
  where
    go :: forall slot 
        .  SlotI Ord slot
       => Proxy slot
       -> ELeaf slot
    go proxy' = ELeaf M.empty

mkStorage :: (AllUniqueLabels slots, AllUniqueLabels (R.Map Proxy slots),
 Forall slots (SlotI Ord), Forall (R.Map Proxy slots) Default) =>
 Proxy slots ->  EBranch slots
mkStorage proxy = toStorage proxy $ mkProxy  proxy

projProxy :: Proxy (slot :: SlotData) -> Proxy (Project slot)
projProxy Proxy = Proxy 

hmwmbm = projProxy (Proxy @MySlot)

type MySlot = Slot Bool Bool Row1 Maybe 

type Row1 :: Row SlotData 
type Row1 = "rootSlotA" .== Slot Bool Int Empty (Either String)
         .+ "rootSlotB" .== Slot Char Int Row2 Maybe 

type Row2 :: Row SlotData 
type Row2 = "depth1SlotA" .== Slot Rational Double Empty  Maybe 
         .+ "depth1SlotB" .== Slot Int String Row3  (Either Bool)

type Row3 :: Row SlotData 
type Row3 = "depth2SlotA" .== Slot String () Empty  []
 

