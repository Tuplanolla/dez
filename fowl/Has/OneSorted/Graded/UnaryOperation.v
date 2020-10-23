From Maniunfold.Has Require Export
  OneSorted.UnaryOperation TwoSorted.Graded.Function.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded unary operation.
    See [Has.OneSorted.UnaryOperation]. *)

Class HasGrdUnOp {A : Type} (P : A -> Type)
  `{HasUnOp A} : Type :=
  grd_un_op : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdUnOp.

(** TODO Check these superclasses. *)

Section Context.

Context {A : Type} {P : A -> Type} `{HasGrdUnOp A P}.

Global Instance P_P_has_grd_fn : HasGrdFn P P := grd_un_op.

End Context.
