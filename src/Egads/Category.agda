module Egads.Category where

  open import Egads.Prelude

  record IsCategory {o a e} {Obj : Set o} (Hom : (X Y : Obj) → Setoid a e)
                    (id : ∀ {X} → 1ₛ ⟶ Hom X X)
                    (comp : ∀ {X Y Z} → Hom X Y ×ₛ Hom Y Z ⟶ Hom X Z)
                    : Set (o ⊔ a ⊔ e) where
    field
      identity : (∀ {Y Z} → let open Setoid (Hom Y Z) in
                  ∀ g → comp ⟨$⟩ (id ⟨$⟩ tt , g) ≈ g)
               × (∀ {X Y} → let open Setoid (Hom X Y) in
                  ∀ f → comp ⟨$⟩ (f , id ⟨$⟩ tt) ≈ f)
      assoc : ∀ {W X Y Z} → ∀ f (g : let open Setoid (Hom X Y) in Carrier) h →
              let open Setoid (Hom W Z) in
              comp ⟨$⟩ (comp ⟨$⟩ (f , g) , h) ≈ comp ⟨$⟩ (f , comp ⟨$⟩ (g , h))

  record CategoryOverHoms {o a e} {Obj : Set o} (Hom : (X Y : Obj) → Setoid a e)
                          : Set (o ⊔ a ⊔ e) where
    field
      id : ∀ {X} → 1ₛ ⟶ Hom X X
      comp : ∀ {X Y Z} → Hom X Y ×ₛ Hom Y Z ⟶ Hom X Z
      isCategory : IsCategory Hom id comp
    open IsCategory isCategory public

    id′ : ∀ {X} → let open Setoid in Hom X X .Carrier
    id′ = id ⟨$⟩ tt

    infixr 7 _>>_ _>>-cong_
    _>>_ : ∀ {X Y Z} → let open Setoid in
           Hom X Y .Carrier → Hom Y Z .Carrier → Hom X Z .Carrier
    f >> g = comp ⟨$⟩ (f , g)

    _>>-cong_ : ∀ {X Y Z f f′ g g′} →
                let module XY = Setoid (Hom X Y) in
                let module YZ = Setoid (Hom Y Z) in
                let module XZ = Setoid (Hom X Z) in
                f XY.≈ f′ → g YZ.≈ g′ → f >> g XZ.≈ f′ >> g′
    ff >>-cong gg = cong comp (ff , gg)

  record CategoryOverObjs {o} a e (Obj : Set o) : Set (o ⊔ suc (a ⊔ e)) where
    field
      Hom : (X Y : Obj) → Setoid a e
      categoryOverHoms : CategoryOverHoms Hom
    open CategoryOverHoms categoryOverHoms public

    infixr 4 _=>_
    _=>_ : (X Y : Obj) → Set a
    X => Y = Setoid.Carrier (Hom X Y)

    module HomEq {X Y} = Setoid (Hom X Y)

  record Category o a e : Set (suc (o ⊔ a ⊔ e)) where
    field
      Obj : Set o
      categoryOverObjs : CategoryOverObjs a e Obj
    open CategoryOverObjs categoryOverObjs public
