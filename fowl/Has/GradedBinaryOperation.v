From DEZ.Has Require Export
  BinaryOperation
  GradedAction GradedAction.
From DEZ.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded binary operation.
    See [Has.BinaryOperation]. *)

Class HasGrdBinOp (A : Type) (P : A -> Type) `(HasBinOp A) : Type :=
  grd_bin_op : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdBinOp.

(** TODO This again. *)

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdBinOp A P).

Global Instance P_P_has_grd_act_l : HasGrdActL P P bin_op := grd_bin_op.
Global Instance P_P_has_grd_act_r : HasGrdActR P P bin_op := grd_bin_op.

End Context.
