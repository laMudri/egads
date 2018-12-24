module Egads.Category.Product where

  open import Egads.Category
  open import Egads.Category.Functor

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality renaming (id to idₛ)

  open import Level

  open import Relation.Binary

  infixr 7 _×c_

  _×c_ : ∀ {oc ac ec od ad ed} → Category oc ac ec → Category od ad ed →
         Category (oc ⊔ od) (ac ⊔ ad) (ec ⊔ ed)
  C ×c D = record
    { Obj = C .Obj × D .Obj
    ; categoryOverObjs = record
      { Hom = λ where
        (cX , dX) (cY , dY) → C .Hom cX cY ×ₛ D .Hom dX dY
      ; categoryOverHoms = record
        { id = < C .id , D .id >ₛ
        ; comp = < C .comp ∘ (proj₁ₛ ×-⟶ proj₁ₛ)
                 , D .comp ∘ (proj₂ₛ ×-⟶ proj₂ₛ)
                 >ₛ
        ; isCategory = record
          { identity = λ where
            .proj₁ (cg , dg) → C .identity .proj₁ cg , D .identity .proj₁ dg
            .proj₂ (cf , df) → C .identity .proj₂ cf , D .identity .proj₂ df
          ; assoc = λ where
            (cf , df) (cg , dg) (ch , dh) →
              C .assoc cf cg ch , D .assoc df dg dh
          }
        }
      }
    }
    where open Category

  <_,_>c : ∀ {oa ob oc aa ab ac ea eb ec} {A : Category oa aa ea}
           {B : Category ob ab eb} {C : Category oc ac ec} →
           A ⇒F B → A ⇒F C → A ⇒F B ×c C
  < F , G >c = record
    { obj = < F .obj , G .obj >
    ; functorOver = record
      { hom = < F .hom , G .hom >ₛ
      ; isFunctor = record
        { hom-id = F .hom-id , G .hom-id
        ; hom-comp = λ f g → F .hom-comp f g , G .hom-comp f g
        }
      }
    }
    where
    open _⇒F_

  proj₁c : ∀ {oa ob aa ab ea eb}
           {A : Category oa aa ea} {B : Category ob ab eb} →
           A ×c B ⇒F A
  proj₁c {A = A} {B} = record
    { obj = proj₁
    ; functorOver = record
      { hom = proj₁ₛ
      ; isFunctor = record
        { hom-id = λ {X} → Setoid.refl (A .Hom (proj₁ X) (proj₁ X))
        ; hom-comp = λ {X} {Y} {Z} f g →
          Setoid.refl (A .Hom (proj₁ X) (proj₁ Z))
        }
      }
    }
    where
    open Category

  proj₂c : ∀ {oa ob aa ab ea eb}
           {A : Category oa aa ea} {B : Category ob ab eb} →
           A ×c B ⇒F B
  proj₂c {A = A} {B} = record
    { obj = proj₂
    ; functorOver = record
      { hom = proj₂ₛ
      ; isFunctor = record
        { hom-id = λ {X} → Setoid.refl (B .Hom (proj₂ X) (proj₂ X))
        ; hom-comp = λ {X} {Y} {Z} f g →
          Setoid.refl (B .Hom (proj₂ X) (proj₂ Z))
        }
      }
    }
    where
    open Category

  map×c : ∀ {oa ob oc od aa ab ac ad ea eb ec ed}
          {A : Category oa aa ea} {B : Category ob ab eb}
          {C : Category oc ac ec} {D : Category od ad ed} →
          A ⇒F C → B ⇒F D → A ×c B ⇒F C ×c D
  map×c F G = < proj₁c >>F F , proj₂c >>F G >c

  assoc×c⃗ : ∀ {oa ob oc aa ab ac ea eb ec} {A : Category oa aa ea}
             {B : Category ob ab eb} {C : Category oc ac ec} →
             (A ×c B) ×c C ⇒F A ×c (B ×c C)
  assoc×c⃗ = < proj₁c >>F proj₁c , < proj₁c >>F proj₂c , proj₂c >c >c

  assoc×c⃖ : ∀ {oa ob oc aa ab ac ea eb ec} {A : Category oa aa ea}
             {B : Category ob ab eb} {C : Category oc ac ec} →
             A ×c (B ×c C) ⇒F (A ×c B) ×c C
  assoc×c⃖ = < < proj₁c , proj₂c >>F proj₁c >c , proj₂c >>F proj₂c >c
