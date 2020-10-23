(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsComm (A : Type) `(HasBinOp A) : Prop :=
  comm : forall x y : A, x + y = y + x.
