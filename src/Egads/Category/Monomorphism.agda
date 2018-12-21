open import Egads.Category

module Egads.Category.Monomorphism {o a e} (C : Category o a e) where

  open Category C

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality hiding (id)

  open import Level

  open import Relation.Binary

  IsMonic : ∀ {X Y : Obj} → X => Y → Set (o ⊔ a ⊔ e)
  IsMonic {X} {Y} g = ∀ {W} {f0 f1 : W => X} →
    let module WY = Setoid (Hom W Y) in
    let module WX = Setoid (Hom W X) in
    f0 >> g WY.≈ f1 >> g → f0 WX.≈ f1

  record Mono (X Y : Obj) : Set (o ⊔ a ⊔ e) where
    field
      g : X => Y
      isMonic : IsMonic g
