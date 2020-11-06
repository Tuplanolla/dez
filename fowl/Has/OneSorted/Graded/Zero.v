From Maniunfold.Has Require Export
  OneSorted.Graded.NullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded zero.
    See [Has.OneSorted.Zero]. *)

Class HasGrdZero (A : Type) (P : A -> Type) `(HasNullOp A) : Type :=
  grd_zero : P 0.

Typeclasses Transparent HasGrdZero.

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdZero A P).

Global Instance P_has_grd_null_op : HasGrdNullOp P null_op := grd_zero.

End Context.
