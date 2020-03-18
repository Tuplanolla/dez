From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Meet OneSorted.Bottom OneSorted.Top.

Declare Scope lattice_scope.

Delimit Scope lattice_scope with lattice.

Open Scope lattice_scope.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '\/' y" (at level 85, right associativity).
Reserved Notation "x '/\' y" (at level 80, right associativity).

Notation "x '\/' y" := (join x y) : lattice_scope.
Notation "x '/\' y" := (meet x y) : lattice_scope.

Reserved Notation "'_|_'" (at level 0, no associativity).
Reserved Notation "'`|`'" (at level 0, no associativity).

Notation "'_|_'" := bot : lattice_scope.
Notation "'`|`'" := top : lattice_scope.
