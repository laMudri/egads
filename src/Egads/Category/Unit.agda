module Egads.Category.Unit where

  open import Egads.Category
  open import Egads.Category.Functor

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality renaming (id to idₛ)

  open import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  1c : Category zero zero zero
  1c = record
    { Obj = ⊤
    ; categoryOverObjs = record
      { Hom = λ _ _ → 1ₛ
      ; categoryOverHoms = record
        { id = const tt
        ; comp = const tt
        ; isCategory = record
          { identity = λ where
            .proj₁ g → refl
            .proj₂ f → refl
          ; assoc = λ f g h → refl
          }
        }
      }
    }

  !c : ∀ {o a e} {C : Category o a e} → C ⇒F 1c
  !c {C = C} = record
    { obj = λ _ → tt
    ; functorOver = record
      { hom = const tt
      ; isFunctor = record
        { hom-id = refl
        ; hom-comp = λ f g → refl
        }
      }
    }
