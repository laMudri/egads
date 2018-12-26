module Egads.Category.Op where

  open import Egads.Prelude

  open import Egads.Category
  open import Egads.Category.Functor

  open import Function using (flip)

  op : ∀ {o a e} → Category o a e → Category o a e
  op C = record
    { Obj = Obj
    ; categoryOverObjs = record
      { Hom = flip Hom
      ; categoryOverHoms = record
        { id = id
        ; comp = comp ∘ₛ swapₛ
        ; isCategory = record
          { identity = λ where
            .proj₁ → identity .proj₂
            .proj₂ → identity .proj₁
          ; assoc = λ f g h → sym (assoc h g f)
          }
        }
      }
    }
    where
    open Category C
    open HomEq

  infixl 9 _ᵒᵖ
  _ᵒᵖ = op

  opF : ∀ {oc od ac ad ec ed} {C : Category oc ac ec} {D : Category od ad ed} →
        C ⇒F D → C ᵒᵖ ⇒F D ᵒᵖ
  opF F = record
    { obj = obj
    ; functorOver = record
      { hom = hom
      ; isFunctor = record
        { hom-id = hom-id
        ; hom-comp = flip hom-comp
        }
      }
    }
    where open _⇒F_ F
