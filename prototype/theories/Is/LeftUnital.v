From Maniunfold.Has Require Export
  EquivalenceRelation ExternalBinaryOperation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftUnital {A B : Type} {has_eq_rel : HasEqRel B}
  (has_op : HasExBiOp A B) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_unital : forall x : B, 0 <+ x == x;
}.
