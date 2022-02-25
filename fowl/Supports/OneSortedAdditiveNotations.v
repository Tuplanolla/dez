From DEZ.Has Require Import
  BinaryOperation NullaryOperation
  UnaryOperation.

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
