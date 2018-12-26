module Egads.Structure where

  open import Egads.Prelude

  open import Egads.Category
  open import Egads.Category.Groupoid
  open import Egads.Category.Isomorphism

  Monoid : ∀ a e → Set (suc (a ⊔ e))
  Monoid a e = CategoryOverObjs a e ⊤

  module Monoid {a e} (M : Monoid a e) where
    open CategoryOverObjs M public
    open Setoid (Hom tt tt) public

    category : Category zero a e
    category = record { categoryOverObjs = M }

  record Group a e : Set (suc (a ⊔ e)) where
    field
      monoid : Monoid a e
    open Monoid monoid public
    field
      allIso : ∀ f → IsIso category f

    open AllIso _ allIso public

    groupoid : Groupoid zero a e
    groupoid = record { category = category ; allIso = allIso }
