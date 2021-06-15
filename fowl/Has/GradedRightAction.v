From Maniunfold.Has Require Export
  BinaryOperation ThreeSortedGradedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded action; right chirality.
    See [Has.OneSorted.Action]. *)

Class HasGrdActR (A : Type) (P Q : A -> Type) `(HasBinOp A) : Type :=
  grd_act_r : forall i j : A, Q i -> P j -> Q (i + j).

Typeclasses Transparent HasGrdActR.

Section Context.

Context (A : Type) (P Q : A -> Type) `(HasGrdActR A P Q).

Global Instance Q_P_Q_has_grd_bin_fn : HasGrdBinFn Q P Q bin_op := grd_act_r.

End Context.
