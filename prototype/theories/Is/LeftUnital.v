From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftUnital {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBiOp A) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_unital : forall x : A, 0 + x == x;
}.
