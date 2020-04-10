From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One OneSorted.Reciprocation.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '+' y" (at level 50, left associativity).
Reserved Notation "'0'" (at level 0, no associativity).
Reserved Notation "'-' x" (at level 35, right associativity).
Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "'1'" (at level 0, no associativity).
Reserved Notation "'/' x" (at level 35, right associativity).

Declare Scope ring_scope.

Delimit Scope ring_scope with ring.

Open Scope ring_scope.

Notation "x '+' y" := (add x y) : ring_scope.
Notation "'0'" := zero : ring_scope.
Notation "'-' x" := (neg x) : ring_scope.
Notation "x '*' y" := (mul x y) : ring_scope.
Notation "'1'" := one : ring_scope.
Notation "'/' x" := (recip x) : ring_scope.
