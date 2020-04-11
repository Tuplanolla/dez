From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.
From Maniunfold.Is Require Export
  Categorical.Associative Categorical.Magmoid.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsScat (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) : Prop := {
  A_comp_is_cat_assoc :> IsCatAssoc A comp;
  A_comp_is_magd :> IsMagd A comp;
}.
