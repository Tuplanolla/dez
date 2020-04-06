(* bad *)
From Maniunfold.Has.Categorical Require Export
  Morphism Composition.
From Maniunfold.Is.Categorically Require Export
  Associative Magmoid.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsScat {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) : Prop := {
  comp_is_cat_assoc :> IsCatAssoc comp;
  comp_is_magd :> IsMagd comp;
}.
