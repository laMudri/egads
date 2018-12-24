-- _×c_ is a monoidal product

module Egads.Category.Monoidal.Cartesian where

  open import Egads.Category
  open import Egads.Category.Functor
  open import Egads.Category.Lift
  open import Egads.Category.Monoidal
  open import Egads.Category.NaturalTransformation
  open import Egads.Category.Product
  open import Egads.Category.SmallCategories
  open import Egads.Category.Unit

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality hiding (id)

  open import Level

  open import Relation.Binary

  ×F : ∀ {o a e} → CAT o a e ×c CAT o a e ⇒F CAT o a e
  ×F {o} {a} {e} = record
    { obj = uncurry _×c_
    ; functorOver = record
      { hom = record
        { _⟨$⟩_ = uncurry map×c
        ; cong = λ where
          (F , G) → record
            { α = record
              { η = F .η , G .η
              ; square = λ where (f , g) → F .square f , G .square g
              }
            ; isNaturalIso = record
              { f⁻¹ = F .η⁻¹ , G .η⁻¹
              ; f-f⁻¹ = F .η-η⁻¹ , G .η-η⁻¹
              ; f⁻¹-f = F .η⁻¹-η , G .η⁻¹-η
              }
            }
        }
      ; isFunctor = let open Category in record
        { hom-id = λ where
          {C , D} → record
            { α = record { _⇒N_ (idN {F = idF {C = C ×c D}}) }
            ; isNaturalIso = id≈N {F = idF {C = C ×c D}} .isNaturalIso
            }
        ; hom-comp = λ where
          {C₀ , D₀} {C₁ , D₁} {C₂ , D₂} (F , G) (F′ , G′) → record
            { α = record { _⇒N_ (idN {F = (map×c F G) >>F (map×c F′ G′)}) }
            ; isNaturalIso = id≈N {F = (map×c F G) >>F (map×c F′ G′)}
                                  .isNaturalIso
            }
        }
      }
    }
    where
    open _≈N_

  -- CAT is monoidal with unit 1c and tensor _×c_
  CAT-monCat : ∀ o a e → MonCat (suc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e)
  CAT-monCat o a e = record
    { Cat = CAT o a e
    ; isMonoidal = record
      { unit = constF (liftF o a e .obj 1c)
      ; tensor = ×F
      ; monoidalProperties = record
        { unitor = λ where
          .proj₁ → record
            { α = record
              { η = proj₂c
              ; square = λ {C} {D} F → record
                { α = record
                  { _⇒N_ (idN {F = proj₂c {A = liftF o a e .obj 1c} {C} >>F F})
                  }
                ; isNaturalIso =
                  id≈N {F = proj₂c {A = liftF o a e .obj 1c} {C} >>F F}
                       .isNaturalIso
                }
              }
            ; isNaturalIso = λ {C} → record
              { f⁻¹ = < constF (lift tt) , idF >c
              ; f-f⁻¹ = record
                { α = record
                  { _⇒N_ (idN {F = idF {C = liftF o a e .obj 1c ×c C}}) }
                ; isNaturalIso =
                  id≈N {F = idF {C = liftF o a e .obj 1c ×c C}} .isNaturalIso
                }
              ; f⁻¹-f = record
                { α = record { _⇒N_ (idN {F = idF {C = C}}) }
                ; isNaturalIso = id≈N {F = idF {C = C}} .isNaturalIso
                }
              }
            }
          .proj₂ → record
            { α = record
              { η = proj₁c
              ; square = λ {C} {D} F → record
                { α = record
                  { _⇒N_ (idN {F = proj₁c {A = C} {liftF o a e .obj 1c} >>F F})
                  }
                ; isNaturalIso =
                  id≈N {F = proj₁c {A = C} {liftF o a e .obj 1c} >>F F}
                       .isNaturalIso
                }
              }
            ; isNaturalIso = λ {C} → record
              { f⁻¹ = < idF , constF (lift tt) >c
              ; f-f⁻¹ = record
                { α = record
                  { _⇒N_ (idN {F = idF {C = C ×c liftF o a e .obj 1c}}) }
                ; isNaturalIso =
                  id≈N {F = idF {C = C ×c liftF o a e .obj 1c}} .isNaturalIso
                }
              ; f⁻¹-f = record
                { α = record { _⇒N_ (idN {F = idF {C = C}}) }
                ; isNaturalIso = id≈N {F = idF {C = C}} .isNaturalIso
                }
              }
            }
        ; associator = record
          { α = record
            { η = assoc×c⃗
            ; square = λ where
              ((F , G) , H) → record
                { α = record
                  { _⇒N_ (idN {F = assoc×c⃗ >>F map×c F (map×c G H)}) }
                ; isNaturalIso =
                  id≈N {F = assoc×c⃗ >>F map×c F (map×c G H)} .isNaturalIso
                }
            }
          ; isNaturalIso = λ where
            {(A , B) , C} → record
              { f⁻¹ = assoc×c⃖
              ; f-f⁻¹ = record
                { α = record
                  { _⇒N_ (idN {F = assoc×c⃗ >>F assoc×c⃖ {A = A} {B} {C}}) }
                ; isNaturalIso =
                  id≈N {F = assoc×c⃗ >>F assoc×c⃖ {A = A} {B} {C}} .isNaturalIso
                }
              ; f⁻¹-f = record
                { α = record
                  { _⇒N_ (idN {F = assoc×c⃖ >>F assoc×c⃗ {A = A} {B} {C}}) }
                ; isNaturalIso =
                  id≈N {F = assoc×c⃖ >>F assoc×c⃗ {A = A} {B} {C}} .isNaturalIso
                }
              }
          }
        }
      }
    }
    where
    open Category
    open _⇒F_
    open _⇒N_
    open _≈N_
