open import Egads.Category

module Egads.Category.Endofunctor {o a e} (C : Category o a e) where

  open import Egads.Prelude

  open import Egads.Category.Functor
  open import Egads.Category.Isomorphism
  open import Egads.Category.Monoidal
  open import Egads.Category.NaturalTransformation
  open import Egads.Category.Product
  open import Egads.Category.SmallCategories
  open import Egads.Category.Unit

  private
    module CAT {o a e} where
      open Category (CAT o a e) public
      open HomEq public

  Endofunctor = C ⇒F C

  Endofunctor-monCat : MonCat (o ⊔ a ⊔ e) (o ⊔ a ⊔ e) (o ⊔ e)
  Endofunctor-monCat = record
    { Cat = C ⇒Fc C
    ; isMonoidal = record
      { unit = constF idF
      ; tensor = record
        { obj = uncurry _>>F_
        ; functorOver = record
          { hom = horiz-compN
          ; isFunctor = record
            { hom-id = λ where
              {F , G} → begin⟨ Hom _ _ ⟩
                (idN {F = F} vvN idN {F = G}) .η  ≈⟨ refl ⟩
                (G .hom ⟨$⟩ idN {F = F} .η) >> idN {F = G} .η
                                             ≈⟨ identity .proj₂ _ ⟩
                (G .hom ⟨$⟩ idN {F = F} .η)  ≈⟨ G .hom-id ⟩
                idN {F = F >>F G} .η  ∎
            ; hom-comp = λ where
              {F₀ , G₀} {F₁ , G₁} {F₂ , G₂} (α , β) (α′ , β′) →
                begin⟨ Hom _ _ ⟩
                ((α >>N α′) vvN (β >>N β′)) .η  ≈⟨ refl ⟩
                (G₀ .hom ⟨$⟩ (α >>N α′) .η) >> (β >>N β′) .η  ≈⟨ refl ⟩
                (G₀ .hom ⟨$⟩ (α .η >> α′ .η)) >> (β .η >> β′ .η)
                  ≈⟨ G₀ .hom-comp _ _ >>-cong refl ⟩
                ((G₀ .hom ⟨$⟩ α .η) >> (G₀ .hom ⟨$⟩ α′ .η)) >> (β .η >> β′ .η)
                  ≈⟨ assoc _ _ _ ⟩
                (G₀ .hom ⟨$⟩ α .η) >> ((G₀ .hom ⟨$⟩ α′ .η) >> (β .η >> β′ .η))
                  ≈⟨ refl >>-cong sym (assoc _ _ _) ⟩
                (G₀ .hom ⟨$⟩ α .η) >> (((G₀ .hom ⟨$⟩ α′ .η) >> β .η) >> β′ .η)
                  ≈⟨ refl >>-cong β .square _ >>-cong refl ⟩
                (G₀ .hom ⟨$⟩ α .η) >> ((β .η >> (G₁ .hom ⟨$⟩ α′ .η)) >> β′ .η)
                  ≈⟨ refl >>-cong assoc _ _ _ ⟩
                (G₀ .hom ⟨$⟩ α .η) >> (β .η >> ((G₁ .hom ⟨$⟩ α′ .η) >> β′ .η))
                  ≈⟨ sym (assoc _ _ _) ⟩
                ((G₀ .hom ⟨$⟩ α .η) >> β .η) >> ((G₁ .hom ⟨$⟩ α′ .η) >> β′ .η)
                  ≈⟨ refl ⟩
                (α vvN β) .η >> (α′ vvN β′) .η  ≈⟨ refl ⟩
                ((α vvN β) >>N (α′ vvN β′)) .η  ∎
            }
          }
        }
      ; monoidalProperties = record
        { unitor = λ where
          .proj₁ → record
            { α = record
              { η = λ {G} → record { _⇒N_ (idN {F = G}) }
              ; square = λ {G} {G′} β → begin⟨ Hom _ _ ⟩
                ((G .hom ⟨$⟩ id′) >> β .η) >> id′  ≈⟨ identity .proj₂ _ ⟩
                (G .hom ⟨$⟩ id′) >> β .η           ≈⟨ G .hom-id >>-cong refl ⟩
                id′ >> β .η                        ∎
              }
            ; isNaturalIso = λ {F} → record
              { f⁻¹ = record { η = id′ ; square = idN {F = F} .square }
              ; Boring F
              }
            }
          .proj₂ → record
            { α = record
              { η = λ {F} → record { _⇒N_ (idN {F = F}) }
              ; square = λ {F} {F′} α → begin⟨ Hom _ _ ⟩
                (α .η >> id′) >> id′  ≈⟨ identity .proj₂ _ ⟩
                α .η >> id′           ≈⟨ identity .proj₂ _ ⟩
                    α .η              ≈⟨ sym (identity .proj₁ _) ⟩
                id′ >> α .η           ∎
              }
            ; isNaturalIso = λ {G} → record
              { f⁻¹ = record { η = id′ ; square = idN {F = G} .square }
              ; Boring G
              }
            }
        ; associator = record
          { α = record
            { η = λ where
              {(F , G) , H} .η → id′
              {(F , G) , H} .square → idN {F = F >>F G >>F H} .square
            ; square = λ where
              {(F , G) , H} {(F′ , G′) , H′} ((α , β) , γ) → begin⟨ Hom _ _ ⟩
                ((α vvN β) vvN γ) .η >> id′  ≈⟨ identity .proj₂ _ ⟩
                ((α vvN β) vvN γ) .η         ≈⟨ refl ⟩
                (H .hom ⟨$⟩ (G .hom ⟨$⟩ α .η) >> β .η) >> γ .η
                                             ≈⟨ H .hom-comp _ _ >>-cong refl ⟩
                ((H .hom ⟨$⟩ (G .hom ⟨$⟩ α .η)) >> (H .hom ⟨$⟩ β .η)) >> γ .η
                                             ≈⟨ assoc _ _ _ ⟩
                (H .hom ⟨$⟩ (G .hom ⟨$⟩ α .η)) >> (H .hom ⟨$⟩ β .η)  >> γ .η
                                             ≈⟨ refl ⟩
                (α vvN (β vvN γ)) .η         ≈⟨ sym (identity .proj₁ _) ⟩
                id′ >> (α vvN (β vvN γ)) .η  ∎
            }
          ; isNaturalIso = λ where
            {(F , G) , H} → record
              { f⁻¹ = record
                { η = id′
                ; square = idN {F = F >>F G >>F H} .square
                }
              ; Boring (F >>F G >>F H)
              }
          }
        }
      }
    }
    where
    open Category C
    open HomEq
    open _⇒F_
    open _⇒N_
    open _≈N_

    module Boring (F : C ⇒F C) = _≈N_ (id≈N {F = F}) using ()
      renaming (η⁻¹ to f⁻¹; η-η⁻¹ to f-f⁻¹; η⁻¹-η to f⁻¹-f)
