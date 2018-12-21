open import Egads.Category

module Egads.Category.Isomorphism {o a e} (C : Category o a e) where

  open Category C

  open import Egads.Category.Monomorphism C
  open import Egads.Category.Epimorphism C

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function using (_on_)
  open import Function.Equality hiding (id)

  open import Level

  open import Relation.Binary
  import Relation.Binary.On as On
  open import Relation.Binary.SetoidReasoning

  record IsIso {X Y : Obj} (f : X => Y) : Set (a ⊔ e) where
    field
      f⁻¹ : Y => X
      f-f⁻¹ : let open Setoid (Hom X X) in f >> f⁻¹ ≈ id′
      f⁻¹-f : let open Setoid (Hom Y Y) in f⁻¹ >> f ≈ id′

    f-isMonic : IsMonic f
    f-isMonic {W} {f0} {f1} eq = begin⟨ Hom W X ⟩
      f0                ≈⟨ sym (identity .proj₂ f0) ⟩
      f0 >>    id′      ≈⟨ refl >>-cong sym f-f⁻¹ ⟩
      f0 >> (f >> f⁻¹)  ≈⟨ sym (assoc f0 f f⁻¹) ⟩
      (f0 >> f) >> f⁻¹  ≈⟨ eq >>-cong refl ⟩
      (f1 >> f) >> f⁻¹  ≈⟨ assoc f1 f f⁻¹ ⟩
      f1 >> (f >> f⁻¹)  ≈⟨ refl >>-cong f-f⁻¹ ⟩
      f1 >>    id′      ≈⟨ identity .proj₂ f1 ⟩
      f1                ∎
      where
      open HomEq

    f-isEpic : IsEpic f
    f-isEpic {Z} {g0} {g1} eq = begin⟨ Hom Y Z ⟩
                    g0  ≈⟨ sym (identity .proj₁ g0) ⟩
           id′   >> g0  ≈⟨ sym f⁻¹-f >>-cong refl ⟩
      (f⁻¹ >> f) >> g0  ≈⟨ assoc f⁻¹ f g0 ⟩
      f⁻¹ >> (f >> g0)  ≈⟨ refl >>-cong eq ⟩
      f⁻¹ >> (f >> g1)  ≈⟨ sym (assoc f⁻¹ f g1) ⟩
      (f⁻¹ >> f) >> g1  ≈⟨ f⁻¹-f >>-cong refl ⟩
           id′   >> g1  ≈⟨ identity .proj₁ g1 ⟩
                    g1  ∎
      where
      open HomEq

    f⁻¹-isIso : IsIso f⁻¹
    f⁻¹-isIso = record { f⁻¹ = f ; f-f⁻¹ = f⁻¹-f ; f⁻¹-f = f-f⁻¹ }

  module IsIso⁻¹ {X Y} {f : X => Y} (f-isIso : IsIso f) where
    open IsIso f-isIso using (f⁻¹-isIso)
    open IsIso f⁻¹-isIso public using ()
      renaming (f-isMonic to f⁻¹-isMonic; f-isEpic to f⁻¹-isEpic)

  record _=≈_ (X Y : Obj) : Set (a ⊔ e) where
    field
      f : X => Y
      isIso : IsIso f
    open IsIso isIso public
    open IsIso⁻¹ isIso public

  symI : ∀ {X Y} → X =≈ Y → Y =≈ X
  symI i = record
    { f = f⁻¹
    ; isIso = record
      { f⁻¹ = f
      ; f-f⁻¹ = f⁻¹-f
      ; f⁻¹-f = f-f⁻¹
      }
    }
    where open _=≈_ i

  Iso : (X Y : Obj) → Setoid (a ⊔ e) e
  Iso X Y = record
    { Carrier = X =≈ Y
    ; _≈_ = _≈_ on _=≈_.f
    ; isEquivalence = On.isEquivalence _=≈_.f isEquivalence
    }
    where open Setoid (Hom X Y)

  AllIso : Set (o ⊔ a ⊔ e)
  AllIso = ∀ {X Y} (f : X => Y) → IsIso f

  module AllIso-Core (allIso : AllIso) {X Y} (f : X => Y) where
    private
      module M = IsIso (allIso f)

    open M public hiding (f⁻¹)
    open M using (f⁻¹)

    infixl 8 _⁻¹
    _⁻¹ : Y => X
    _⁻¹ = f⁻¹

  module AllIso (allIso : AllIso) where
    open AllIso-Core allIso public

    module _ {X : Obj} where
      open Setoid (Hom X X)

      id⁻¹ : id′ ⁻¹ ≈ id′ {X}
      id⁻¹ = trans (sym (identity .proj₁ (id′ ⁻¹))) (f-f⁻¹ id′)

    module _ {X Y Z : Obj} where
      module Dummy {A B : Obj} = Setoid (Hom A B)
      open Dummy

      >>⁻¹ : (f : X => Y) (g : Y => Z) → (f >> g) ⁻¹ ≈ g ⁻¹ >> f ⁻¹
      >>⁻¹ f g = f-isMonic (f >> g) (begin⟨ Hom Z Z ⟩
        (f >> g) ⁻¹ >> (f >> g)  ≈⟨ f⁻¹-f (f >> g) ⟩
        id′  ≈⟨ sym (f⁻¹-f g) ⟩
        g ⁻¹ >> g  ≈⟨ sym (refl >>-cong identity .proj₁ g) ⟩
        g ⁻¹ >> (id′ >> g)  ≈⟨ sym (refl >>-cong (f⁻¹-f f >>-cong refl)) ⟩
        g ⁻¹ >> ((f ⁻¹ >> f) >> g)  ≈⟨ refl >>-cong assoc _ _ _ ⟩
        g ⁻¹ >> (f ⁻¹ >> (f >> g))  ≈⟨ sym (assoc _ _ _) ⟩
        (g ⁻¹ >> f ⁻¹) >> (f >> g)  ∎)
