(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsUnAbsorb (A : Type)
  (A_has_null_op : HasNullOp A) (A_has_un_op : HasUnOp A) : Prop :=
  un_absorb : - 0 = 0.
