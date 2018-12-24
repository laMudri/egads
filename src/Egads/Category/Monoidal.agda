module Egads.Category.Monoidal where

  open import Egads.Category
  open import Egads.Category.Functor
  open import Egads.Category.NaturalTransformation
  open import Egads.Category.Unit
  open import Egads.Category.Product

  open import Data.Product
  open import Data.Product.Relation.Pointwise.NonDependent
  open import Data.Unit renaming (setoid to 1ₛ)

  open import Function.Equality hiding (id)

  open import Level

  open import Relation.Binary

  module _ {o a e} (C : Category o a e) where
    open Category C
    open _⇒F_

    record MonoidalProperties (unit : 1c ⇒F C) (tensor : C ×c C ⇒F C)
                              : Set (o ⊔ a ⊔ e) where
      field
        unitor : < !c >>F unit , idF >c >>F tensor ≈N idF
               × < idF , !c >>F unit >c >>F tensor ≈N idF
        associator : _≈N_ {C = (C ×c C) ×c C} {C}
                          (map×c tensor idF >>F tensor)
                          (assoc×c⃗ >>F map×c idF tensor >>F tensor)

    record IsMonoidal : Set (o ⊔ a ⊔ e) where
      field
        unit : 1c ⇒F C
        tensor : C ×c C ⇒F C
        monoidalProperties : MonoidalProperties unit tensor
      open MonoidalProperties monoidalProperties public

      I : Obj
      I = unit .obj tt

      _⊗_ : (X Y : Obj) → Obj
      X ⊗ Y = tensor .obj (X , Y)

  record MonCat o a e : Set (suc (o ⊔ a ⊔ e)) where
    field
      Cat : Category o a e
      isMonoidal : IsMonoidal Cat
    open Category Cat public
    open IsMonoidal isMonoidal public
