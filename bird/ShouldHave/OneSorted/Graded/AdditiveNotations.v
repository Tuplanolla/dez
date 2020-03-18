From Maniunfold.Has Require Export
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation
  OneSorted.Graded.UnaryOperation.

Declare Scope group_scope.

Delimit Scope group_scope with group.

Open Scope group_scope.

Reserved Notation "x 'G+' y" (at level 50, left associativity).
Reserved Notation "'G0'" (at level 0, no associativity).
Reserved Notation "'G-' x" (at level 35, right associativity).

Notation "x 'G+' y" := (grd_bin_op _ _ x y) : group_scope.
Notation "'G0'" := grd_null_op : group_scope.
Notation "'G-' x" := (grd_un_op _ x) : group_scope.
