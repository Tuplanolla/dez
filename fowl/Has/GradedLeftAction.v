From Maniunfold.Has Require Export
  BinaryOperation ThreeSortedGradedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded action; left chirality.
    See [Has.OneSorted.Action]. *)

Class HasGrdActL (A : Type) (P Q : A -> Type) `(HasBinOp A) : Type :=
  grd_act_l : forall i j : A, P i -> Q j -> Q (i + j).

Typeclasses Transparent HasGrdActL.

Section Context.

Context (A : Type) (P Q : A -> Type) `(HasGrdActL A P Q).

Global Instance P_Q_Q_has_grd_bin_fn : HasGrdBinFn P Q Q bin_op := grd_act_l.

End Context.
