From Maniunfold.Has Require Export
  UnaryOperation TwoSortedGradedGradedFunction.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded unary operation.
    See [Has.UnaryOperation]. *)

Class HasGrdUnOp (A : Type) (P : A -> Type) `(HasUnOp A) : Type :=
  grd_un_op : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdUnOp.

(** TODO Check these superclasses. *)

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdUnOp A P).

Global Instance P_P_has_grd_fn : HasGrdFn P P un_op := grd_un_op.

End Context.
