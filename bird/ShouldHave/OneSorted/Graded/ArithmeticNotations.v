From Maniunfold.Has Require Export
  OneSorted.Graded.Addition OneSorted.Graded.Zero OneSorted.Graded.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  OneSorted.Graded.Reciprocation.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '+' y" (at level 50, left associativity).
Reserved Notation "'0'" (at level 0, no associativity).
Reserved Notation "'-' x" (at level 35, right associativity).
Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "'1'" (at level 0, no associativity).
Reserved Notation "'/' x" (at level 35, right associativity).

Declare Scope grd_ring_scope.

Delimit Scope grd_ring_scope with grd_ring.

Open Scope grd_ring_scope.

Notation "x '+' y" := (grd_add _ _ x y) : grd_ring_scope.
Notation "'0'" := grd_zero : grd_ring_scope.
Notation "'-' x" := (grd_neg _ x) : grd_ring_scope.
Notation "x '*' y" := (grd_mul _ _ x y) : grd_ring_scope.
Notation "'1'" := grd_one : grd_ring_scope.
Notation "'/' x" := (grd_recip _ x) : grd_ring_scope.
