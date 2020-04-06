From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.

Declare Scope group_scope.

Delimit Scope group_scope with group.

Open Scope group_scope.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "'1'" (at level 0, no associativity).
Reserved Notation "'/' x" (at level 35, right associativity).

Notation "x '*' y" := (bin_op x y) : group_scope.
Notation "'1'" := null_op : group_scope.
Notation "'/' x" := (un_op x) : group_scope.
