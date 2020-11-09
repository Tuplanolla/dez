From Maniunfold.Has Require Export
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation
  OneSorted.Graded.UnaryOperation.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '+' y" (at level 50, left associativity).
Reserved Notation "'0'" (at level 0, no associativity).
Reserved Notation "'-' x" (at level 35, right associativity).

Reserved Notation "'_+_'" (at level 0, no associativity).
Reserved Notation "'-_'" (at level 0, no associativity).

Declare Scope grd_grp_scope.

Delimit Scope grd_grp_scope with grd_grp.

Open Scope grd_grp_scope.

Notation "x '+' y" := (grd_bin_op _ _ x y) : grd_grp_scope.
Notation "'_+_'" := (grd_bin_op _ _) (only parsing) : grd_grp_scope.
Notation "'0'" := grd_null_op : grd_grp_scope.
Notation "'-' x" := (grd_un_op _ x) : grd_grp_scope.
Notation "'-_'" := (grd_un_op _) (only parsing) : grd_grp_scope.
