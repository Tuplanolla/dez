From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '+' y" (at level 50, left associativity).
Reserved Notation "'0'" (at level 0, no associativity).
Reserved Notation "'-' x" (at level 35, right associativity).

Declare Scope grp_scope.

Delimit Scope grp_scope with grp.

Open Scope grp_scope.

Notation "x '+' y" := (bin_op x y) : grp_scope.
Notation "'0'" := null_op : grp_scope.
Notation "'-' x" := (un_op x) : grp_scope.
