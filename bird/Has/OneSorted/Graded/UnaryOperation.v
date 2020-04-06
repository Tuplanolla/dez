(* bad *)
From Maniunfold.Has Require Export
  OneSorted.NullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class HasGrdUnOp {A : Type} (P : A -> Type)
  {A_has_un_op : HasUnOp A} : Type :=
  grd_un_op : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdUnOp.
