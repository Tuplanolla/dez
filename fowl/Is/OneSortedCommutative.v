(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsComm (A : Type) `(HasBinOp A) : Prop :=
  comm : forall x y : A, x + y = y + x.
