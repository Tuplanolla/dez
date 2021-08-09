From DEZ.Has Require Import
  GradedBinaryOperation GradedNullaryOperation
  GradedUnaryOperation.

Declare Scope grd_grp_scope.

Delimit Scope grd_grp_scope with grd_grp.

Open Scope grd_grp_scope.

Notation "x '*' y" := (grd_bin_op _ _ x y) : grd_grp_scope.
Notation "'1'" := grd_null_op : grd_grp_scope.
Notation "'/' x" := (grd_un_op _ x) : grd_grp_scope.

Notation "'_*_'" := (grd_bin_op _ _) (only parsing) : grd_grp_scope.
Notation "'/_'" := (grd_un_op _) (only parsing) : grd_grp_scope.
