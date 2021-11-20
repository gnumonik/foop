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
      Row )
import GHC.TypeLits (Symbol, TypeError)
import Data.Row.Dictionaries (mapHas)

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
lookupStorage :: forall label slots slot
               . SlotKey label slots slot
              -> Rec (R.Map StorageBox slots)
              -> StorageBox slot
lookupStorage key@SlotKey storage = withDict (deriveHas @StorageBox key) $ storage .! (Label @label)



modifyStorage :: forall label slots slot
               . SlotKey label slots slot
              -> (StorageBox slot -> StorageBox slot)
              -> Rec (R.Map StorageBox slots)
              -> Rec (R.Map StorageBox slots)
modifyStorage key@SlotKey f storage
  = withDict (deriveHas @StorageBox key)
  $ R.update (Label @label) (f $ storage .! (Label @label)) storage

mkProxy :: ( AllUniqueLabels slots
         , AllUniqueLabels (R.Map Proxy slots)
         , Forall (R.Map Proxy slots) Default
         ) => Proxy (slots :: Row SlotData)
           -> Rec (R.Map Proxy slots)
mkProxy Proxy = R.default' @Default def

type TestRow = "slot1" .== Slot Int String Empty Maybe
            .+ "slot2" .== Slot String Int Empty Maybe

instance Default (Proxy (a :: k)) where
  def = Proxy

toStorage :: forall slots. (Forall slots SlotOrdC)
          => Proxy slots
          -> Rec (R.Map Proxy slots)
          -> Rec (R.Map StorageBox slots)
toStorage proxy = R.transform @SlotOrdC @slots @Proxy @StorageBox go
  where
    go :: forall slot
        . Proxy slot
       -> StorageBox slot
    go proxy' =  MkStorageBox M.empty





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

mkStorage :: (AllUniqueLabels slots, AllUniqueLabels (R.Map Proxy slots),
 Forall slots SlotOrdC, Forall (R.Map Proxy slots) Default) =>
 Proxy slots -> Rec (R.Map StorageBox slots)
mkStorage proxy = toStorage proxy $ mkProxy  proxy

type MySlot = Slot Bool Bool Row1 Maybe 

type Row1 :: Row SlotData 
type Row1 = "rootSlotA" .== Slot Bool Int Empty (Either String)
         .+ "rootSlotB" .== Slot Char Int Row2 Maybe 

type Row2 :: Row SlotData 
type Row2 = "depth1SlotA" .== Slot Rational Double Empty  Maybe 
         .+ "depth1SlotB" .== Slot Int String Row3  (Either Bool)

type Row3 :: Row SlotData 
type Row3 = "depth2SlotA" .== Slot String () Empty  []
 

