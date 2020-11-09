From Maniunfold.Offers Require Export
  OneSorted.Arithmetic.
From Maniunfold.ShouldHave Require Export
  OneSorted.ArithmeticNotations.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '-' y" (at level 50, left associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).

Reserved Notation "'_-_'" (at level 0, no associativity).
Reserved Notation "'_/_'" (at level 0, no associativity).

Notation "x '-' y" := (sub _ _ x y) : ring_scope.
Notation "'_-_'" := (sub _ _) (only parsing) : ring_scope.
Notation "x '/' y" := (div _ _ x y) : ring_scope.
Notation "'_/_'" := (div _ _) (only parsing) : ring_scope.
