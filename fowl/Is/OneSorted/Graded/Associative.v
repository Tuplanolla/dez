(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Associative.
From Maniunfold.ShouldHave Require Import
  OneSorted.Graded.AdditiveNotations.

Class IsGrdAssoc (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_assoc :> IsAssoc bin_op;
  grd_assoc : forall (i j k : A) (x : P i) (y : P j) (z : P k),
    rew assoc i j k in (x + (y + z)) = (x + y) + z;
}.
