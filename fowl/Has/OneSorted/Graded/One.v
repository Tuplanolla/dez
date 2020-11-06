From Maniunfold.Has Require Export
  OneSorted.Graded.NullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded one.
    See [Has.OneSorted.One]. *)

Class HasGrdOne (A : Type) (P : A -> Type) `(HasNullOp A) : Type :=
  grd_one : P 0.

Typeclasses Transparent HasGrdOne.

Section Context.

Context (A : Type) (P : A -> Type) `(HasGrdOne A P).

Global Instance P_has_grd_null_op : HasGrdNullOp P null_op := grd_one.

End Context.
