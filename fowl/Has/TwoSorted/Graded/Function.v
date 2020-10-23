From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded function.
    See [Has.TwoSorted.Function]. *)

Class HasGrdFn {A : Type} (P Q : A -> Type)
  `{HasUnOp A} : Type :=
  grd_fn : forall i : A, P i -> Q (- i).

Typeclasses Transparent HasGrdFn.
