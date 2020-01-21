From Maniunfold.Has Require Export
  BinaryRelation BinaryFunction Unit Function.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRExtInv {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_bin_fn : HasBinFn A B C) (has_un : HasUn C)
  (has_fn : HasFn A B) : Prop :=
  r_ext_inv : forall x : A, x >+< >-< x ~~ 0.
