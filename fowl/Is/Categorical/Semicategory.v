From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.
From Maniunfold.Is Require Export
  Categorical.Associative Categorical.Magmoid.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsScat (A : Type) `{HasHom A}
  `(HasComp A) : Prop := {
  A_comp_is_cat_assoc :> IsCatAssoc comp;
  A_comp_is_magd :> IsMagd comp;
}.
