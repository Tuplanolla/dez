(* bad *)
From Maniunfold.Has Require Export
  OneSortedNullaryOperation OneSortedUnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsUnAbsorb (A : Type)
  `(HasNullOp A) `(HasUnOp A) : Prop :=
  un_absorb : - 0 = 0.
