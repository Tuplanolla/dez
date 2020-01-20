From Maniunfold.Has Require Export
  EquivalenceRelation BinaryFunction Unit Function.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLExtInv {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_bin_fn : HasBinFn B A C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop := {
  eq_rel_is_eq :> IsEq eq_rel;
  l_ext_inv : forall x : A, >-< x >+< x == 0;
}.
