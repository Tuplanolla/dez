From Maniunfold.Has Require Export
  OneSortedBinaryRelation.

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Reserved Notation "x '~~' y" (no associativity, at level 70).

Notation "x '~~' y" := (bin_rel x y) : rel_scope.

Notation "'_~~_'" := bin_rel (only parsing) : rel_scope.
