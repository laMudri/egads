open import Egads.Category

module Egads.Category.Epimorphism {o a e} (C : Category o a e) where

  open Category C

  open import Egads.Prelude

  open import Egads.Category.Op
  open import Egads.Category.Monomorphism (C ᵒᵖ)

  IsEpic : ∀ {X Y : Obj} → X => Y → Set (o ⊔ a ⊔ e)
  IsEpic = IsMonic  -- in C ᵒᵖ

  record Epi (X Y : Obj) : Set (o ⊔ a ⊔ e) where
    field
      f : X => Y
      isEpic : IsEpic f
