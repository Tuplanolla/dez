(* bad *)
From DEZ.Has Require Export
  BinaryOperation GradedBinaryOperation.
From DEZ.Is Require Export
  Associative.
From DEZ.ShouldHave Require Import
  OneSortedGradedAdditiveNotations.

Class IsGrdAssoc (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_assoc :> IsAssoc bin_op;
  grd_assoc : forall (i j k : A) (x : P i) (y : P j) (z : P k),
    rew assoc i j k in (x + (y + z)) = (x + y) + z;
}.
