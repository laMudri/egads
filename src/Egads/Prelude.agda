-- Stuff from stdlib that I need all the time

module Egads.Prelude where

  open import Data.Product public
  open import Data.Product.Relation.Pointwise.NonDependent public
  open import Data.Unit renaming (setoid to 1ₛ) public

  open import Function.Equality public
    hiding (setoid)
    renaming (id to idₛ; _∘_ to _∘ₛ_; flip to flipₛ)

  open import Level public

  open import Relation.Binary using (Rel; Setoid; IsEquivalence) public
  open import Relation.Binary.SetoidReasoning public
