module Egads.Category.Groupoid where

  open import Egads.Category
  open import Egads.Category.Isomorphism

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality hiding (id; setoid)

  open import Level

  open import Relation.Binary
  import Relation.Binary.EqReasoning as EqR

  record Groupoid o a e : Set (suc (o ⊔ a ⊔ e)) where
    field
      category : Category o a e
      allIso : AllIso category
    open Category category public
    open AllIso _ allIso public

    -- Forget the content of the arrows
    setoid : Setoid o a
    setoid = record
      { Carrier = Obj
      ; _≈_ = _=>_
      ; isEquivalence = record
        { refl = id′
        ; sym = _⁻¹
        ; trans = _>>_
        }
      }

  core : ∀ {o a e} → Category o a e → Groupoid o (a ⊔ e) e
  core C = record
    { category = record
      { Obj = Obj
      ; categoryOverObjs = record
        { Hom = Iso C
        ; categoryOverHoms = record
          { id = const (record
            { f = id′
            ; isIso = record
              { f⁻¹ = id′
              ; f-f⁻¹ = identity .proj₁ id′
              ; f⁻¹-f = identity .proj₁ id′
              }
            })
          ; comp = λ {X} {Y} {Z} → record
            { _⟨$⟩_ = λ where
              (i , j) .f → i .f >> j .f
              (i , j) .isIso .f⁻¹ → j .f⁻¹ >> i .f⁻¹
              (i , j) .isIso .f-f⁻¹ → let open EqR (Hom X X) in begin
                (i .f >> j .f) >> (j .f⁻¹ >> i .f⁻¹)  ≈⟨ sym (assoc _ _ _) ⟩
                ((i .f >> j .f) >> j .f⁻¹) >> i .f⁻¹
                  ≈⟨ assoc _ _ _ >>-cong refl ⟩
                (i .f >> (j .f >> j .f⁻¹)) >> i .f⁻¹
                  ≈⟨ (refl >>-cong j .f-f⁻¹) >>-cong refl ⟩
                (i .f >> id′) >> i .f⁻¹  ≈⟨ identity .proj₂ _ >>-cong refl ⟩
                i .f >> i .f⁻¹  ≈⟨ i .f-f⁻¹ ⟩
                id′  ∎
              (i , j) .isIso .f⁻¹-f → let open EqR (Hom Z Z) in begin
                (j .f⁻¹ >> i .f⁻¹) >> (i .f >> j .f)  ≈⟨ sym (assoc _ _ _) ⟩
                ((j .f⁻¹ >> i .f⁻¹) >> i .f) >> j .f
                  ≈⟨ assoc _ _ _ >>-cong refl ⟩
                (j .f⁻¹ >> (i .f⁻¹ >> i .f)) >> j .f
                  ≈⟨ (refl >>-cong i .f⁻¹-f) >>-cong refl ⟩
                (j .f⁻¹ >> id′) >> j .f  ≈⟨ identity .proj₂ _ >>-cong refl ⟩
                j .f⁻¹ >> j .f  ≈⟨ j .f⁻¹-f ⟩
                id′  ∎
            ; cong = cong comp
            }
          ; isCategory = record
            { identity =
              λ where
              .proj₁ j → identity .proj₁ (j .f)
              .proj₂ i → identity .proj₂ (i .f)
            ; assoc = λ i j k → assoc (i .f) (j .f) (k .f)
            }
          }
        }
      }
    ; allIso = λ i → record
      { f⁻¹ = symI C i
      ; f-f⁻¹ = i .f-f⁻¹
      ; f⁻¹-f = i .f⁻¹-f
      }
    }
    where
    open Category C
    open HomEq
    open _=≈_
    open IsIso
