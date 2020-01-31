From Maniunfold.Has Require Export
  BinaryRelation BinaryFunction Unit Function.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLIntInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn A B C) (has_un : HasUn C)
  (has_fn : HasFn B A) : Prop :=
  l_int_inv : forall x : B, T- x T+ x ~~ T0.
