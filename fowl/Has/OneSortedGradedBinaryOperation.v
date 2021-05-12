From Maniunfold.Has Require Export
  OneSortedBinaryOperation
  TwoSortedGradedLeftAction TwoSortedGradedRightAction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded binary operation.
    See [Has.OneSortedBinaryOperation]. *)

Class HasGrdBinOp (A : Type) (P : A -> Type) `(HasBinOp A) : Type :=
  grd_bin_op : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdBinOp.

(** TODO This again. *)

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdBinOp A P).

Global Instance P_P_has_grd_l_act : HasGrdLAct P P bin_op := grd_bin_op.
Global Instance P_P_has_grd_r_act : HasGrdRAct P P bin_op := grd_bin_op.

End Context.
