From Maniunfold.Has Require Export
  OneSorted.BinaryRelation BinaryFunction Unit Function.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRIntInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn B A C) (has_un : HasUn C)
  (has_fn : HasFn B A) : Prop :=
  r_int_inv : forall x : B, x T+ T- x ~~ T0.
