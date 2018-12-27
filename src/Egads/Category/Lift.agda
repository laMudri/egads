module Egads.Category.Lift where

  open import Egads.Prelude

  open import Egads.Category
  open import Egads.Category.Functor
  open import Egads.Category.NaturalTransformation
  open import Egads.Category.SmallCategories

  liftF : ∀ {o a e} ol al el → CAT o a e ⇒F CAT (o ⊔ ol) (a ⊔ al) (e ⊔ el)
  liftF ol al el = record
    { obj = λ C → let open Category C in record
      { Obj = Lift ol Obj
      ; categoryOverObjs = record
        { Hom = λ where
          (lift X) (lift Y) .Carrier → Lift al (Hom X Y .Carrier)
          (lift X) (lift Y) ._≈_ (lift f) (lift g) →
            Lift el (Hom X Y ._≈_ f g)
          (lift X) (lift Y) .isEquivalence .refl → lift (Hom X Y .refl)
          (lift X) (lift Y) .isEquivalence .sym (lift fg) →
            lift (Hom X Y .sym fg)
          (lift X) (lift Y) .isEquivalence .trans (lift fg) (lift gh) →
            lift (Hom X Y .trans fg gh)
        ; categoryOverHoms = record
          { id = record { _⟨$⟩_ = λ x → lift (id ⟨$⟩ x)
                        ; cong = λ xx → lift (id .cong xx)
                        }
          ; comp = record
            { _⟨$⟩_ = λ { (lift f , lift g) → lift (comp ⟨$⟩ (f , g)) }
            ; cong = λ { (lift ff , lift gg) → lift (comp .cong (ff , gg)) }
            }
          ; isCategory = record
            { identity = λ where
              .proj₁ (lift g) → lift (identity .proj₁ g)
              .proj₂ (lift f) → lift (identity .proj₂ f)
            ; assoc = λ where
              (lift f) (lift g) (lift h) → lift (assoc f g h)
            }
          }
        }
      }
    ; functorOver = record
      { hom = record
        { _⟨$⟩_ = λ F → let open _⇒F_ F in record
          { obj = λ where (lift X) → lift (obj X)
          ; functorOver = record
            { hom = record
              { _⟨$⟩_ = λ where (lift f) → lift (hom ⟨$⟩ f)
              ; cong = λ where (lift ff) → lift (hom .cong ff)
              }
            ; isFunctor = record
              { hom-id = lift hom-id
              ; hom-comp = λ where (lift f) (lift g) → lift (hom-comp f g)
              }
            }
          }
        ; cong = λ FF → record
          { α = record { η = lift (FF .η)
                       ; square = λ where (lift f) → lift (FF .square f)
                       }
          ; isNaturalIso = record
            { f⁻¹ = lift (FF .η⁻¹)
            ; f-f⁻¹ = lift (FF .η-η⁻¹)
            ; f⁻¹-f = lift (FF .η⁻¹-η)
            }
          }
        }
      ; isFunctor = record
        { hom-id = λ {C} → let open Category C in record
          { α = record
            { η = lift id′
            ; square = λ where
              (lift f) → lift (idN {F = idF {C = C}} .square f)
            }
          ; isNaturalIso = record
            { f⁻¹ = lift id′
            ; f-f⁻¹ = lift (identity .proj₁ _)
            ; f⁻¹-f = lift (identity .proj₁ _)
            }
          }
        ; hom-comp = λ {A} {B} {C} F G → let open Category C in record
          { α = record
            { η = lift id′
            ; square = λ where (lift f) → lift (idN {F = F >>F G} .square f)
            }
          ; isNaturalIso = record
            { f⁻¹ = lift id′
            ; f-f⁻¹ = lift (identity .proj₁ _)
            ; f⁻¹-f = lift (identity .proj₁ _)
            }
          }
        }
      }
    }
    where
    open Setoid
    open IsEquivalence
    open _≈N_
    open _⇒N_
