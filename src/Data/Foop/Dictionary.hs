module Data.Foop.Dictionary where

import Data.Foop.Types ( SlotKey(..), StorageBox, RenderBranch, SlotC, SlotOrdC, IndexOf )
import Data.Constraint ( Dict(..), mapDict, weaken1, withDict )
import Data.Row ( HasType, type (.!) )
import qualified Data.Row.Records as R
import Data.Row.Dictionaries ( mapHas )

deriveStoreHas :: forall label slots slot
                . SlotKey label slots slot
               -> Dict (HasType label (StorageBox slot) (R.Map StorageBox slots))
deriveStoreHas SlotKey
  = withDict
    (mapDict weaken1 $ mapDict (mapHas @StorageBox @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict

storeHas :: forall label slots slot
          . ( HasType label slot slots 
          --  , SlotC (slots .! label),
            ,  R.Forall slots SlotOrdC,
              Ord (IndexOf (slots .! label)),
              R.KnownSymbol label) 
         =>   Dict (HasType  label (StorageBox (slots .! label)) (R.Map StorageBox slots))
storeHas  = withDict
    (mapDict weaken1 $ mapDict (mapHas @StorageBox @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict

deriveSurfaceHas :: forall label slots slot
                  . SlotKey label slots slot
                 -> Dict (HasType label (RenderBranch slot) (R.Map RenderBranch slots))
deriveSurfaceHas SlotKey
  = withDict
    (mapDict weaken1 $ mapDict (mapHas @RenderBranch @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict