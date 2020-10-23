(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsUnAbsorb (A : Type)
  `(HasNullOp A) `(HasUnOp A) : Prop :=
  un_absorb : - 0 = 0.
