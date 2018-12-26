module Relation.Binary.Prop where

  open import Data.Product

  open import Function

  open import Level

  open import Relation.Binary

  Prop : ∀ a → Setoid (suc a) a
  Prop a = record
    { Carrier = Set a
    ; _≈_ = λ P Q → (P → Q) × (Q → P)
    ; isEquivalence = record
      { refl = id , id
      ; sym = λ { (f , g) → (g , f) }
      ; trans = λ { (f , g) (f′ , g′) → (f′ ∘ f , g ∘ g′) }
      }
    }
