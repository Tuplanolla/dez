From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit EndoFunction.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRightInvertible {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_endo_fn : HasEndoFn A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  right_invertible : forall x : A, x + - x == 0;
}.
