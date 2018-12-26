module Egads.Category.Thin where

  open import Egads.Category

  open import Level

  Thin : ∀ {o a e} → Category o a e → Set (o ⊔ a ⊔ e)
  Thin C = ∀ {X Y} (f g : X => Y) → f ≈ g
    where
    open Category C
    open HomEq
