open import Egads.Category

module Egads.Category.Hom {o a e} (C : Category o a e) where

  open import Egads.Prelude

  open import Egads.Category.Functor
  open import Egads.Category.Op
  open import Egads.Category.Product
  open import Egads.Category.Setoid

  open Category C
  open HomEq

  HomF : C ᵒᵖ ×c C ⇒F SETOID a e
  HomF = record
    { obj = uncurry Hom
    ; functorOver = record
      { hom = λ where
        ._⟨$⟩_ (f , h) ._⟨$⟩_ g → f >> g >> h
        ._⟨$⟩_ (f , h) .cong gg → refl >>-cong gg >>-cong refl
        .cong (ff , hh) gg → ff >>-cong gg >>-cong hh
      ; isFunctor = record
        { hom-id = λ where
          {X , Y} {f} {f′} ff → begin⟨ Hom X Y ⟩
            id′ >> f >> id′  ≈⟨ refl >>-cong identity .proj₂ f ⟩
            id′ >> f         ≈⟨ identity .proj₁ f ⟩
                   f         ≈⟨ ff ⟩
                   f′        ∎
        ; hom-comp = λ where
          {X₁ , X₂} {Y₁ , Y₂} {Z₁ , Z₂} (f₁ , h₁) (f₂ , h₂) {g} {g′} gg →
            begin⟨ Hom Z₁ Z₂ ⟩
              (f₂ >> f₁) >> g  >> (h₁ >> h₂)  ≈⟨ refl >>-cong gg >>-cong refl ⟩
              (f₂ >> f₁) >> g′ >> (h₁ >> h₂)  ≈⟨ refl >>-cong
                                                 sym (assoc _ _ _) ⟩
              (f₂ >> f₁) >> (g′ >> h₁) >> h₂  ≈⟨ sym (assoc _ _ _) ⟩
              ((f₂ >> f₁) >> (g′ >> h₁)) >> h₂  ≈⟨ assoc _ _ _ >>-cong refl ⟩
              (f₂ >> (f₁ >> (g′ >> h₁))) >> h₂  ≈⟨ assoc _ _ _ ⟩
              f₂ >> (f₁ >> g′ >> h₁) >> h₂  ∎
        }
      }
    }
