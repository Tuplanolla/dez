From Maniunfold.Has Require Export
  BinaryOperation OneSortedNullaryOperation
  OneSortedUnaryOperation.

Declare Scope grp_scope.

Delimit Scope grp_scope with grp.

Open Scope grp_scope.

Notation "'_+_'" := bin_op : grp_scope.
#[deprecated(since="now")]
Notation "x '+' y" := (bin_op x y) : grp_scope.
#[deprecated(since="now")]
Notation "'0'" := null_op : grp_scope.
Notation "'-_'" := un_op : grp_scope.
#[deprecated(since="now")]
Notation "'-' x" := (un_op x) : grp_scope.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Notation "'_+_'" := bin_op : algebra_scope.
Notation "x '+' y" := (bin_op x y) : algebra_scope.
Notation "'0'" := null_op : algebra_scope.
Notation "'-_'" := un_op : algebra_scope.
Notation "'-' x" := (un_op x) : algebra_scope.
