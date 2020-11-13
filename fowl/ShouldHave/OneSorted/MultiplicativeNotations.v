From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.UnaryOperation.

Declare Scope grp_scope.

Delimit Scope grp_scope with grp.

Open Scope grp_scope.

Notation "x '*' y" := (bin_op x y) : grp_scope.
Notation "'1'" := null_op : grp_scope.
Notation "'/' x" := (un_op x) : grp_scope.

Notation "'_*_'" := bin_op (only parsing) : grp_scope.
Notation "'/_'" := un_op (only parsing) : grp_scope.
