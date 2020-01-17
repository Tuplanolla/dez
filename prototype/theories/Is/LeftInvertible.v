From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit EndoFunction.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftInvertible {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBiOp A) (has_un : HasUn A)
  (has_endo_fn : HasEndoFn A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_invertible : forall x : A, - x + x == 0;
}.
