From DEZ.Has Require Export
  NullaryOperation.
From DEZ.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Graded nullary operation.
    See [Has.NullaryOperation]. *)

Class HasGrdNullOp (A : Type) (P : A -> Type) `(HasNullOp A) : Type :=
  grd_null_op : P 0.

Typeclasses Transparent HasGrdNullOp.
