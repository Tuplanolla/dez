(* bad *)
From Maniunfold.Offers Require Export
  OneSorted.Arithmetic.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

Declare Scope ring_scope.

Delimit Scope ring_scope with ring.

Open Scope ring_scope.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '-' y" (at level 50, left associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).

Notation "x '-' y" := (sub x y) : ring_scope.
Notation "x '/' y" := (div x y) : ring_scope.
