(* bad *)
From Maniunfold.Has Require Export
  Addition ThreeSortedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsRBiaddve (A B C : Type)
  `(HasAdd B) `(HasAdd C)
  `(HasBinFn A B C) : Prop :=
  r_biaddve : forall (x : A) (y z : B),
    bin_fn x (y + z) = bin_fn x y + bin_fn x z.
