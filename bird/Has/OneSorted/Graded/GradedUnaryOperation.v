From Maniunfold.Has Require Export
  UnaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class HasGrdUnOp (A : Type) (P : A -> Type) {has_un_op : HasUnOp A} : Type :=
  grd_un_op : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdUnOp.
