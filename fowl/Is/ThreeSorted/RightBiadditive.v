(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition ThreeSorted.BinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRBiaddve (A B C : Type)
  (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  r_biaddve : forall (x : A) (y z : B),
    bin_fn x (y + z) = bin_fn x y + bin_fn x z.
