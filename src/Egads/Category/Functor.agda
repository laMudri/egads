module Egads.Category.Functor where

  open import Egads.Category

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function renaming (id to id→)
  open import Function.Equality renaming (id to idₛ; _∘_ to _∘ₛ_)

  open import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

  module _ {oc ac ec od ad ed} (C : Category oc ac ec) (D : Category od ad ed)
           where
    open Category

    record IsFunctor (obj : C .Obj → D .Obj)
                     (hom : ∀ {X Y} → C .Hom X Y ⟶ D .Hom (obj X) (obj Y))
                     : Set (oc ⊔ ac ⊔ ed) where
      private
        module C = Category C
      field
        hom-id : ∀ {X} → let open Setoid (D .Hom (obj X) (obj X)) in
                 hom ⟨$⟩ (C .id {X} ⟨$⟩ tt) ≈ D .id ⟨$⟩ tt
        hom-comp : ∀ {X Y Z} (f : X C.=> Y) (g : Y C.=> Z) →
                   let open Setoid (D .Hom (obj X) (obj Z)) in
                   hom ⟨$⟩ (C .comp ⟨$⟩ (f , g)) ≈
                     D .comp ⟨$⟩ (hom ⟨$⟩ f , hom ⟨$⟩ g)

    record FunctorOver (obj : C .Obj → D .Obj)
                       : Set (oc ⊔ ac ⊔ ec ⊔ ad ⊔ ed) where
      field
        hom : ∀ {X Y} → C .Hom X Y ⟶ D .Hom (obj X) (obj Y)
        isFunctor : IsFunctor obj hom
      open IsFunctor isFunctor public

    infixr 2 _⇒F_

    record _⇒F_ : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      field
        obj : C .Obj → D .Obj
        functorOver : FunctorOver obj
      open FunctorOver functorOver public

  idF : ∀ {o a e} {C : Category o a e} → C ⇒F C
  idF {C = C} = record
    { obj = id→
    ; functorOver = record
      { hom = idₛ
      ; isFunctor = record
        { hom-id = λ {X} → Setoid.refl (Hom X X)
        ; hom-comp = λ {X} {Y} {Z} f g → Setoid.refl (Hom X Z)
        }
      }
    }
    where
    open Category C

  infixr 9 _>>F_

  _>>F_ : ∀ {oa ob oc aa ab ac ea eb ec} {A : Category oa aa ea}
         {B : Category ob ab eb} {C : Category oc ac ec} →
         A ⇒F B → B ⇒F C → A ⇒F C
  _>>F_ {A = A} {B} {C} F G = record
    { obj = GF
    ; functorOver = record
      { hom = G .hom ∘ₛ F .hom
      ; isFunctor = record
        { hom-id = λ {X} → let open Setoid (Hom (GF X) (GF X)) in
                           trans (cong (G .hom) (F .hom-id))
                                 (G .hom-id)
        ; hom-comp = λ {X} {Y} {Z} f g →
          let open Setoid (Hom (GF X) (GF Z)) in
          trans (cong (G .hom) (F .hom-comp f g))
                (G .hom-comp (F .hom ⟨$⟩ f) (F .hom ⟨$⟩ g))
        }
      }
    }
    where
    open _⇒F_
    open Category C
    GF = G .obj ∘ F .obj
