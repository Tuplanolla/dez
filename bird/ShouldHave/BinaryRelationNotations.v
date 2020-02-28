From Maniunfold.Has Require Export
  TwoSorted.BinaryRelation.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Reserved Notation "x '~~' y" (at level 70, no associativity).
Notation "x '~~' y" := (bin_rel_2 x y) : algebra_scope.

Reserved Notation "x '~/~' y" (at level 70, no associativity).
Notation "x '~/~' y" := (not (bin_rel_2 x y)) : algebra_scope.
