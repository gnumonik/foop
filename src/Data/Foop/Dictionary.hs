module Data.Foop.Dictionary where

import Data.Foop.Types 
import Data.Constraint ( Dict(..), mapDict, weaken1, withDict )
import Data.Row ( HasType, type (.!) )
import qualified Data.Row.Records as R
import Data.Row.Dictionaries ( mapHas )

deriveHas :: forall f label slots slot
                . SlotKey label slots slot
               -> Dict (HasType label (f slot) (R.Map f slots))
deriveHas SlotKey 
  = withDict
    (mapDict weaken1 $ mapDict (mapHas @f @label @slot @slots) (Dict @((slots .! label) ~ slot)))
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

{--
deriveSurfaceHas :: forall label slots slot
                  . RootKey label slots slot
                 -> Dict (HasType label (RenderBranch slot) (R.Map RenderBranch slots))
deriveSurfaceHas RootKey
  = withDict
    (mapDict weaken1 $ mapDict (mapHas @RenderBranch @label @slot @slots) (Dict @((slots .! label) ~ slot)))
    Dict
--}