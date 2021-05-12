From Maniunfold.Has Require Export
  OneSortedUnaryOperation OneSortedGradedUnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded negation.
    See [Has.OneSortedNegation]. *)

Class HasGrdNeg (A : Type) (P : A -> Type) `(HasUnOp A) : Type :=
  grd_neg : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdNeg.

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdNeg A P).

Global Instance P_has_grd_un_op : HasGrdUnOp P un_op := grd_neg.

End Context.
