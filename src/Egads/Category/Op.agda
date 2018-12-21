module Egads.Category.Op where

  open import Egads.Category

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit

  open import Function hiding (id; _∘_)
  open import Function.Equality hiding (id; flip)

  open import Relation.Binary

  op : ∀ {o a e} → Category o a e → Category o a e
  op C = record
    { Obj = Obj
    ; categoryOverObjs = record
      { Hom = flip Hom
      ; categoryOverHoms = record
        { id = id
        ; comp = comp ∘ swapₛ
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
