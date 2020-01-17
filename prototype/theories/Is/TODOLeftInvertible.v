From Maniunfold.Has Require Export
  EquivalenceRelation BinaryFunction Unit Function.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftInvertible {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_bi_fn : HasBiFn B A C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_invertible : forall x : A, (>-< x) >+< x == 0;
}.
