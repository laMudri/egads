module Egads.Category.Adjunction where

  open import Egads.Prelude

  open import Egads.Category
  open import Egads.Category.Functor
  open import Egads.Category.Hom
  open import Egads.Category.Lift
  open import Egads.Category.NaturalTransformation
  open import Egads.Category.Op
  open import Egads.Category.Product
  open import Egads.Category.Setoid

  module _ {o a e} {C : Category o a e} {D : Category o a e} where
    _⊣_ : C ⇒F D → D ⇒F C → Set (o ⊔ a ⊔ e)
    L ⊣ R = _≈N_ {C = C ᵒᵖ ×c D} {D = SETOID a e}
      (map×c (opF L) idF >>F HomF D)
      (map×c idF R >>F HomF C)
