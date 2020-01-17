From Maniunfold.Has Require Export
  EquivalenceRelation BinaryFunction Unit Function.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRightInvertible {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_bi_fn : HasBinFn A B C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  right_invertible : forall x : A, x >+< (>-< x) == 0;
}.
