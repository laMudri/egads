module Egads.Order where

  open import Egads.Prelude

  open import Egads.Category
  open import Egads.Category.Thin

  open import Relation.Binary.Simple

  record Preorder (o a e : Level) : Set (suc (o ⊔ a) ⊔ e) where
    field
      Obj : Set o
      _=>_ : (X Y : Obj) → Set a

    Hom : (X Y : Obj) → Setoid a e
    Hom X Y = Always-setoid (X => Y)

    field
      categoryOverHoms : CategoryOverHoms Hom

    categoryOverObjs : CategoryOverObjs a e Obj
    categoryOverObjs = record { categoryOverHoms = categoryOverHoms }

    category : Category o a e
    category = record { categoryOverObjs = categoryOverObjs }
    open Category category public using (id; comp; id′; _>>_)

    thin : Thin category
    thin f g = lift tt
