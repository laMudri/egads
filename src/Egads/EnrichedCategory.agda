open import Egads.Category
open import Egads.Category.Monoidal

module Egads.EnrichedCategory {ov av ev} (V : MonCat ov av ev) where
  private
    module V = MonCat V
  open V using (_=>_; module HomEq; id′; _>>_; I; _⊗_; unit; tensor
               ; unitor; associator)
  open HomEq

  open import Egads.Prelude

  open import Egads.Category.Functor
  open import Egads.Category.NaturalTransformation

  open _⇒F_
  open _≈N_

  record IsEnrichedCat {o} {Obj : Set o} (Hom : (X Y : Obj) → V.Obj)
                       (id : ∀ {X} → I => Hom X X)
                       (comp : ∀ {X Y Z} → Hom X Y ⊗ Hom Y Z => Hom X Z)
                       : Set (ev ⊔ o) where
    field
      identity : (∀ {Y Z} → unitor .proj₁ .η⁻¹
                         >> (tensor .hom ⟨$⟩ (id , id′ {Hom Y Z})) >> comp
                          ≈ id′)
               × (∀ {X Y} → unitor .proj₂ .η⁻¹
                         >> (tensor .hom ⟨$⟩ (id′ {Hom X Y} , id)) >> comp
                          ≈ id′)
      assoc : ∀ {W X Y Z} → associator .η⁻¹
                         >> (tensor .hom ⟨$⟩ (comp {W} {X} {Y} , id′)) >> comp
                          ≈ (tensor .hom ⟨$⟩ (id′ , comp {X} {Y} {Z})) >> comp

  record EnrichedCatOverHoms {o} {Obj : Set o} (Hom : (X Y : Obj) → V.Obj)
                             : Set (av ⊔ ev ⊔ o) where
    field
      id : ∀ {X} → I => Hom X X
      comp : ∀ {X Y Z} → Hom X Y ⊗ Hom Y Z => Hom X Z
      isEnrichedCat : IsEnrichedCat Hom id comp
    open IsEnrichedCat isEnrichedCat public

  record EnrichedCatOverObjs {o} (Obj : Set o) : Set (ov ⊔ av ⊔ ev ⊔ o) where
    field
      Hom : (X Y : Obj) → V.Obj
      enrichedCatOverHoms : EnrichedCatOverHoms Hom
    open EnrichedCatOverHoms enrichedCatOverHoms public

  record EnrichedCat o : Set (ov ⊔ av ⊔ ev ⊔ suc o) where
    field
      Obj : Set o
      enrichedCatOverObjs : EnrichedCatOverObjs Obj
    open EnrichedCatOverObjs enrichedCatOverObjs public
