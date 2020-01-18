From Maniunfold.Has Require Export
  EquivalenceRelation BinaryFunction Unit Function.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftExternallyInvertible {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_bin_fn : HasBinFn B A C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_externally_invertible : forall x : A, >-< x >+< x == 0;
}.
