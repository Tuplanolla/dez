From Maniunfold.Has Require Export
  OneSortedBinaryOperation ThreeSortedGradedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded action; left chirality.
    See [Has.OneSorted.LeftAction]. *)

Class HasGrdLAct (A : Type) (P Q : A -> Type) `(HasBinOp A) : Type :=
  grd_l_act : forall i j : A, P i -> Q j -> Q (i + j).

Typeclasses Transparent HasGrdLAct.

Section Context.

Context (A : Type) (P Q : A -> Type) `(HasGrdLAct A P Q).

Global Instance P_Q_Q_has_grd_bin_fn : HasGrdBinFn P Q Q bin_op := grd_l_act.

End Context.
