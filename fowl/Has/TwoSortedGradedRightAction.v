From Maniunfold.Has Require Export
  OneSortedBinaryOperation ThreeSortedGradedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded action; right chirality.
    See [Has.OneSorted.LeftAction]. *)

Class HasGrdRAct (A : Type) (P Q : A -> Type) `(HasBinOp A) : Type :=
  grd_r_act : forall i j : A, Q i -> P j -> Q (i + j).

Typeclasses Transparent HasGrdRAct.

Section Context.

Context (A : Type) (P Q : A -> Type) `(HasGrdRAct A P Q).

Global Instance Q_P_Q_has_grd_bin_fn : HasGrdBinFn Q P Q bin_op := grd_r_act.

End Context.
