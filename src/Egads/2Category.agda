module Egads.2Category where

  open import Egads.Category
  open import Egads.Category.Monoidal
  open import Egads.Category.Monoidal.Cartesian
  open import Egads.EnrichedCategory

  open import Level

  2Category : ∀ ov av ev o → Set (suc (ov ⊔ av ⊔ ev ⊔ o))
  2Category ov av ev o = EnrichedCat (CAT-monCat ov av ev) o
