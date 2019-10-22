From Maniunfold.Has Require Export
  EquivalenceRelation Relation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.Supports Require Import
  RelationNotations EquivalenceNotations.

Class IsAntisymmetric {A : Type} {has_eqv : HasEqv A}
  (has_rel : HasRel A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  antisymmetric : forall x y : A, x ~ y -> y ~ x -> x == y;
}.

Section Context.

Context {A : Type} `{is_antisymmetric : IsAntisymmetric A}.

Global Instance A_eqv_rel_antisymmetric : Antisymmetric A eqv rel | 0 :=
  antisymmetric.

End Context.
