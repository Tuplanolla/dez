From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Meet OneSorted.Bottom OneSorted.Top.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '\/' y" (at level 85, right associativity).
Reserved Notation "x '/\' y" (at level 80, right associativity).

Reserved Notation "'_|_'" (at level 0, no associativity).
Reserved Notation "'`|`'" (at level 0, no associativity).

Declare Scope lat_scope.

Delimit Scope lat_scope with lat.

Open Scope lat_scope.

Notation "x '\/' y" := (join x y) : lat_scope.
Notation "x '/\' y" := (meet x y) : lat_scope.

Notation "'_|_'" := bot : lat_scope.
Notation "'`|`'" := top : lat_scope.
