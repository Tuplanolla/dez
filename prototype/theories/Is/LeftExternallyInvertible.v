From Maniunfold.Has Require Export
  BinaryRelation BinaryFunction Unit Function.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLExtInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn B A C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop :=
  l_ext_inv : forall x : A, >-< x >+< x ~~ 0.
