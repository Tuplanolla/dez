(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition ThreeSorted.BinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsLBiaddve (A B C : Type)
  (A_has_add : HasAdd A) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  l_biaddve : forall (x y : A) (z : B),
    bin_fn (x + y) z = bin_fn x z + bin_fn y z.
