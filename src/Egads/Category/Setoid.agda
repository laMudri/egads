module Egads.Category.Setoid where

  open import Egads.Prelude

  open import Egads.Category

  open import Function using (flip)

  SETOID : ∀ c l → Category (suc (c ⊔ l)) (c ⊔ l) (c ⊔ l)
  SETOID c l = record
    { Obj = Setoid c l
    ; categoryOverObjs = record
      { Hom = _⇨_
      ; categoryOverHoms = record
        { id = const idₛ
        ; comp = record
          { _⟨$⟩_ = uncurry (flip _∘ₛ_)
          ; cong = λ where
            (ff , gg) xx → gg (ff xx)
          }
        ; isCategory = record
          { identity = λ where
            .proj₁ g xx → cong g xx
            .proj₂ f xx → cong f xx
          ; assoc = λ f g h xx → cong h (cong g (cong f xx))
          }
        }
      }
    }
