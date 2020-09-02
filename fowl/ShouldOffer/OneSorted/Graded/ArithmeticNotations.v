From Maniunfold.Offers Require Export
  OneSorted.Graded.Arithmetic.
From Maniunfold.ShouldHave Require Export
  OneSorted.Graded.ArithmeticNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '-' y" (at level 50, left associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).

Notation "x '-' y" := (grd_sub _ _ x y) : grd_ring_scope.
Notation "x '/' y" := (grd_div _ _ x y) : grd_ring_scope.
