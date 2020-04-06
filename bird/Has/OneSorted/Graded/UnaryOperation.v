From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded unary operation.
    See [Has.OneSorted.UnaryOperation]. *)

Class HasGrdUnOp {A : Type} (P : A -> Type)
  {A_has_un_op : HasUnOp A} : Type :=
  grd_un_op : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdUnOp.
