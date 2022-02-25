(* bad *)
From DEZ.Has Require Export
  Addition ThreeSortedBinaryFunction.
From DEZ.Supports Require Import
  OneSortedArithmeticNotations.

Class IsLBiaddve (A B C : Type)
  `(HasAdd A) `(HasAdd C)
  `(HasBinFn A B C) : Prop :=
  l_biaddve : forall (x y : A) (z : B),
    bin_fn (x + y) z = bin_fn x z + bin_fn y z.
