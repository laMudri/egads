module Egads.Category.SmallCategories where

  open import Egads.Prelude

  open import Egads.Category
  open import Egads.Category.Functor
  open import Egads.Category.Groupoid
  open import Egads.Category.Isomorphism
  open import Egads.Category.NaturalTransformation

  CAT : ∀ o a e → Category (suc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e)
  CAT o a e = record
    { Obj = Category o a e
    ; categoryOverObjs = record
      { Hom = _⇒Fₛ_
      ; categoryOverHoms = record
        { id = const idF
        ; comp = λ {A} {B} {C} →
          let open Category C in
          let open HomEq in
          let module B = Category B in λ where
          ._⟨$⟩_ → uncurry _>>F_
          .cong → uncurry _vv≈N_
        ; isCategory = record
          { identity = λ where
            .proj₁ {C} {D} G → let open Category D in record
              { α = record { _⇒N_ (idN {F = G}) }
              ; isNaturalIso = record
                { f⁻¹ = id′
                ; f-f⁻¹ = identity .proj₁ _
                ; f⁻¹-f = identity .proj₁ _
                }
              }
            .proj₂ {C} {D} F → let open Category D in record
              { α = record { η = id′ ; square = idN {F = F} .square }
              ; isNaturalIso = record
                { f⁻¹ = id′
                ; f-f⁻¹ = identity .proj₁ _
                ; f⁻¹-f = identity .proj₁ _
                }
              }
          ; assoc = λ where
            {A} {B} {C} {D} F G H → let open Category D in
                                    let open HomEq in record
              { α = record { η = id′
                           ; square = idN {F = F >>F G >>F H} .square
                           }
              ; isNaturalIso = record
                { f⁻¹ = id′
                ; f-f⁻¹ = identity .proj₁ _
                ; f⁻¹-f = identity .proj₁ _
                }
              }
          }
        }
      }
    }
    where
    open _⇒F_
    open _⇒N_
    open _≈N_
    open _=≈_
