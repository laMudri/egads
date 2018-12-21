module Egads.Category.NaturalTransformation where

  open import Egads.Category
  open import Egads.Category.Functor
  open import Egads.Category.Isomorphism as Iso using ()
  open import Egads.Category.Groupoid

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality hiding (id; setoid)

  open import Level

  open import Relation.Binary
  open import Relation.Binary.SetoidReasoning

  module _ {oc od ac ad ec ed} {C : Category oc ac ec} {D : Category od ad ed}
           where

    infixr 3 _⇒N_ _≈N_

    record _⇒N_ (F G : C ⇒F D) : Set (oc ⊔ ac ⊔ ad ⊔ ed) where
      private
        module C = Category C
        module D = Category D
      open _⇒F_
      open D.HomEq
      field
        η : ∀ {X} → F .obj X D.=> G .obj X
        square : ∀ {X Y} (f : X C.=> Y) →
                 (F .hom ⟨$⟩ f) D.>> η {Y} ≈ η {X} D.>> (G .hom ⟨$⟩ f)

    _⇒Nₛ_ : (F G : C ⇒F D) → Setoid (oc ⊔ ac ⊔ ad ⊔ ed) (oc ⊔ ed)
    F ⇒Nₛ G = record
      { Carrier = F ⇒N G
      ; _≈_ = λ α β → ∀ {X} → α .η {X} ≈ β .η {X}
      ; isEquivalence = record
        { refl = refl
        ; sym = λ αβ {X} → sym (αβ {X})
        ; trans = λ αβ βγ {X} → trans (αβ {X}) (βγ {X})
        }
      }
      where
      open _⇒N_
      open Category D
      open HomEq

    idN : ∀ {F} → F ⇒N F
    idN {F} = record
      { η = id′
      ; square = λ {X} {Y} f → let open Setoid (Hom (obj X) (obj Y)) in
                               trans (identity .proj₂ (hom ⟨$⟩ f))
                                     (sym (identity .proj₁ (hom ⟨$⟩ f)))
      }
      where
      open Category D
      open _⇒F_ F

    infixr 7 _>>N_
    -- Vertical composition
    _>>N_ : ∀ {F G H} → F ⇒N G → G ⇒N H → F ⇒N H
    _>>N_ {F} {G} {H} α β = record
      { η = α .η >> β .η
      ; square = λ {X} {Y} f → begin⟨ Hom (F .obj X) (H .obj Y) ⟩
        (F .hom ⟨$⟩ f) >> (α .η >> β .η)  ≈⟨ sym (assoc _ _ _) ⟩
        ((F .hom ⟨$⟩ f) >> α .η) >> β .η  ≈⟨ α .square f >>-cong refl ⟩
        (α .η >> (G .hom ⟨$⟩ f)) >> β .η  ≈⟨ assoc _ _ _ ⟩
        α .η >> ((G .hom ⟨$⟩ f) >> β .η)  ≈⟨ refl >>-cong β .square f ⟩
        α .η >> (β .η >> (H .hom ⟨$⟩ f))  ≈⟨ sym (assoc _ _ _) ⟩
        (α .η >> β .η) >> (H .hom ⟨$⟩ f)  ∎
      }
      where
      open Category D
      open HomEq
      open _⇒F_
      open _⇒N_

    IsNaturalIso : {F G : C ⇒F D} (α : F ⇒N G) → Set (oc ⊔ ad ⊔ ed)
    IsNaturalIso α = ∀ {X} → IsIso (η {X})
      where
      open _⇒N_ α
      open Iso D

    record _≈N_ (F G : C ⇒F D) : Set (oc ⊔ ac ⊔ ad ⊔ ed) where
      field
        α : F ⇒N G
        isNaturalIso : IsNaturalIso α
      open _⇒N_ α public
      open module Isos {X} = Iso.IsIso (isNaturalIso {X}) public using ()
        renaming (f⁻¹ to η⁻¹; f⁻¹-f to η⁻¹-η; f-f⁻¹ to η-η⁻¹
                 ; f-isMonic to η-isMonic; f-isEpic to η-isEpic
                 ; f⁻¹-isIso to η⁻¹-isIso)
      open module Isos⁻¹ {X} = Iso.IsIso⁻¹ _ (isNaturalIso {X}) public using ()
        renaming (f⁻¹-isMonic to η⁻¹-isMonic; f⁻¹-isEpic to η⁻¹-isEpic)

      α⁻¹ : G ⇒N F
      α⁻¹ = record
        { η = η⁻¹
        ; square = λ {X} {Y} f → begin⟨ Hom _ _ ⟩
          (G .hom ⟨$⟩ f) >> η⁻¹  ≈⟨ η-isMonic (begin⟨ Hom _ _ ⟩
            ((G .hom ⟨$⟩ f) >> η⁻¹) >> η  ≈⟨ assoc _ _ _ ⟩
            (G .hom ⟨$⟩ f) >> (η⁻¹ >> η)  ≈⟨ refl >>-cong η⁻¹-η ⟩
            (G .hom ⟨$⟩ f) >> id′  ≈⟨ identity .proj₂ _ ⟩
            (G .hom ⟨$⟩ f)  ≈⟨ η-isEpic (begin⟨ Hom _ _ ⟩
              η >> (G .hom ⟨$⟩ f)  ≈⟨ sym (square _) ⟩
              (F .hom ⟨$⟩ f) >> η  ≈⟨ sym (identity .proj₁ _) ⟩
              id′ >> (F .hom ⟨$⟩ f) >> η  ≈⟨ sym η-η⁻¹ >>-cong refl ⟩
              (η >> η⁻¹) >> (F .hom ⟨$⟩ f) >> η  ≈⟨ assoc _ _ _ ⟩
              η >> η⁻¹ >> (F .hom ⟨$⟩ f) >> η  ≈⟨ refl >>-cong
                                                  sym (assoc _ _ _) ⟩
              η >> (η⁻¹ >> (F .hom ⟨$⟩ f)) >> η  ∎) ⟩
            (η⁻¹ >> (F .hom ⟨$⟩ f)) >> η  ∎) ⟩
          η⁻¹ >> (F .hom ⟨$⟩ f)  ∎
        }
        where
        open Category D
        open HomEq
        open _⇒F_
      open _⇒N_ α⁻¹ public using () renaming (square to square⁻¹)

  module _ {oc od ac ad ec ed} (C : Category oc ac ec) (D : Category od ad ed)
           where
    _⇒Fc_ : Category (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed)
                     (oc ⊔ ac ⊔ ad ⊔ ed) (oc ⊔ ed)
    _⇒Fc_ = record
      { Obj = C ⇒F D
      ; categoryOverObjs = record
        { Hom = _⇒Nₛ_
        ; categoryOverHoms = record
          { id = const idN
          ; comp = λ where
            ._⟨$⟩_ (F , G) → F >>N G
            .cong (FF , GG) → cong comp (FF , GG)
          ; isCategory = record
            { identity = λ where
              .proj₁ β → identity .proj₁ (β .η)
              .proj₂ α → identity .proj₂ (α .η)
            ; assoc = λ α β γ → assoc (α .η) (β .η) (γ .η)
            }
          }
        }
      }
      where
      open Category D
      open HomEq
      open _⇒N_

    _⇒Fg_ : Groupoid (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed)
                                (oc ⊔ ac ⊔ ad ⊔ ed) (oc ⊔ ed)
    _⇒Fg_ = core _⇒Fc_
    open Groupoid _⇒Fg_ public using ()
      renaming (setoid to _⇒Fₛ_)

  -- Horizontal composition
  _vvN_ : ∀ {oa ob oc aa ab ac ea eb ec} {A : Category oa aa ea}
          {B : Category ob ab eb} {C : Category oc ac ec}
          {F F′ : A ⇒F B} {G G′ : B ⇒F C} →
          F ⇒N F′ → G ⇒N G′ → (F >>F G) ⇒N (F′ >>F G′)
  _vvN_ {A = A} {B} {C} {F} {F′} {G} {G′} α β = record
    { η = (G .hom ⟨$⟩ α .η) >> β .η
    ; square = λ {X} {Y} f →
      begin⟨ Hom (G .obj (F .obj X)) (G′ .obj (F′ .obj Y)) ⟩
        ((F >>F G) .hom ⟨$⟩ f) >> (G .hom ⟨$⟩ α .η) >> β .η  ≈⟨ refl ⟩
        (G .hom ⟨$⟩ (F .hom ⟨$⟩ f)) >> (G .hom ⟨$⟩ α .η) >> β .η
          ≈⟨ sym (assoc _ _ _) ⟩
        ((G .hom ⟨$⟩ (F .hom ⟨$⟩ f)) >> (G .hom ⟨$⟩ α .η)) >> β .η
          ≈⟨ (begin⟨ Hom (G .obj (F .obj X)) (G .obj (F′ .obj Y)) ⟩
            (G .hom ⟨$⟩ (F .hom ⟨$⟩ f)) >> (G .hom ⟨$⟩ α .η)
              ≈⟨ sym (G .hom-comp _ _) ⟩
            G .hom ⟨$⟩ ((F .hom ⟨$⟩ f) B.>> α .η)
              ≈⟨ G .hom .cong (α .square _) ⟩
            G .hom ⟨$⟩ (α .η B.>> (F′ .hom ⟨$⟩ f))
              ≈⟨ G .hom-comp _ _ ⟩
            (G .hom ⟨$⟩ α .η) >> (G .hom ⟨$⟩ (F′ .hom ⟨$⟩ f))  ∎)
          >>-cong refl ⟩
        ((G .hom ⟨$⟩ α .η) >> (G .hom ⟨$⟩ (F′ .hom ⟨$⟩ f))) >> β .η
          ≈⟨ assoc _ _ _ ⟩
        (G .hom ⟨$⟩ α .η) >> (G .hom ⟨$⟩ (F′ .hom ⟨$⟩ f)) >> β .η
          ≈⟨ refl >>-cong β .square _ ⟩
        (G .hom ⟨$⟩ α .η) >> β .η >> (G′ .hom ⟨$⟩ (F′ .hom ⟨$⟩ f))
          ≈⟨ sym (assoc _ _ _) ⟩
        ((G .hom ⟨$⟩ α .η) >> β .η) >> (G′ .hom ⟨$⟩  (F′ .hom ⟨$⟩ f))
          ≈⟨ refl ⟩
        ((G .hom ⟨$⟩ α .η) >> β .η) >> ((F′ >>F G′) .hom ⟨$⟩ f)  ∎
    }
    where
    module A = Category A
    module B = Category B
    open Category C
    open HomEq
    open _⇒F_
    open _⇒N_

  _vv≈N_ : ∀ {oa ob oc aa ab ac ea eb ec} {A : Category oa aa ea}
          {B : Category ob ab eb} {C : Category oc ac ec}
          {F F′ : A ⇒F B} {G G′ : B ⇒F C} →
          F ≈N F′ → G ≈N G′ → (F >>F G) ≈N (F′ >>F G′)
  _vv≈N_ {A = A} {B} {C} {F} {F′} {G} {G′} ι κ = record
    { α = ι .α vvN κ .α
    ; isNaturalIso = record
      { f⁻¹ = (α⁻¹ ι vvN α⁻¹ κ) .η
      ; f-f⁻¹ =
        begin⟨ Hom _ _ ⟩
        (ι .α vvN κ .α) .η >> (α⁻¹ ι vvN α⁻¹ κ) .η  ≈⟨ refl ⟩
        ((G .hom ⟨$⟩ ι .η) >> κ .η) >> ((G′ .hom ⟨$⟩ ι .η⁻¹) >> κ .η⁻¹)
                                       ≈⟨ refl >>-cong κ .square⁻¹ _ ⟩
        ((G .hom ⟨$⟩ ι .η) >> κ .η) >> (κ .η⁻¹ >> (G .hom ⟨$⟩ ι .η⁻¹))
                                       ≈⟨ assoc _ _ _ ⟩
        (G .hom ⟨$⟩ ι .η) >> κ .η >> (κ .η⁻¹ >> (G .hom ⟨$⟩ ι .η⁻¹))
                                       ≈⟨ refl >>-cong sym (assoc _ _ _) ⟩
        (G .hom ⟨$⟩ ι .η) >> (κ .η >> κ .η⁻¹) >> (G .hom ⟨$⟩ ι .η⁻¹)
                                       ≈⟨ refl >>-cong κ .η-η⁻¹ >>-cong refl ⟩
        (G .hom ⟨$⟩ ι .η) >> id′ >> (G .hom ⟨$⟩ ι .η⁻¹)
                                       ≈⟨ refl >>-cong identity .proj₁ _ ⟩
        (G .hom ⟨$⟩ ι .η) >> (G .hom ⟨$⟩ ι .η⁻¹)  ≈⟨ sym (G .hom-comp _ _) ⟩
        (G .hom ⟨$⟩ ι .η B.>> ι .η⁻¹)  ≈⟨ G .hom .cong (ι .η-η⁻¹) ⟩
        (G .hom ⟨$⟩ B.id′)             ≈⟨ G .hom-id ⟩
        id′                            ∎
      ; f⁻¹-f = begin⟨ Hom _ _ ⟩
        (α⁻¹ ι vvN α⁻¹ κ) .η >> (ι .α vvN κ .α) .η  ≈⟨ refl ⟩
        ((G′ .hom ⟨$⟩ ι .η⁻¹) >> κ .η⁻¹) >> ((G .hom ⟨$⟩ ι .η) >> κ .η)
                                        ≈⟨ refl >>-cong κ .square _ ⟩
        ((G′ .hom ⟨$⟩ ι .η⁻¹) >> κ .η⁻¹) >> (κ .η >> (G′ .hom ⟨$⟩ ι .η))
                                        ≈⟨ assoc _ _ _ ⟩
        (G′ .hom ⟨$⟩ ι .η⁻¹) >> κ .η⁻¹ >> (κ .η >> (G′ .hom ⟨$⟩ ι .η))
                                        ≈⟨ refl >>-cong sym (assoc _ _ _) ⟩
        (G′ .hom ⟨$⟩ ι .η⁻¹) >> (κ .η⁻¹ >> κ .η) >> (G′ .hom ⟨$⟩ ι .η)
                                        ≈⟨ refl >>-cong κ .η⁻¹-η >>-cong refl ⟩
        (G′ .hom ⟨$⟩ ι .η⁻¹) >> id′ >> (G′ .hom ⟨$⟩ ι .η)
                                        ≈⟨ refl >>-cong identity .proj₁ _ ⟩
        (G′ .hom ⟨$⟩ ι .η⁻¹) >> (G′ .hom ⟨$⟩ ι .η)  ≈⟨ sym (G′ .hom-comp _ _) ⟩
        (G′ .hom ⟨$⟩ ι .η⁻¹ B.>> ι .η)  ≈⟨ G′ .hom .cong (ι .η⁻¹-η) ⟩
        (G′ .hom ⟨$⟩ B.id′)             ≈⟨ G′ .hom-id ⟩
        id′                             ∎
      }
    }
    where
    open Category C
    module B = Category B
    open HomEq
    open _⇒F_
    open _≈N_
    open _⇒N_
