From Maniunfold.Has Require Export
  EquivalenceRelation BinaryFunction Unit Function.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRExtInv {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_bin_fn : HasBinFn A B C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop := {
  eq_rel_is_setoid :> IsEq eq_rel;
  right_externally_invertible : forall x : A, x >+< >-< x == 0;
}.
