From Maniunfold.Has Require Export
  BinaryRelation.

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Reserved Notation "x '~~' y" (no associativity, at level 70).

Notation "'_~~_'" := bin_rel : rel_scope.
Notation "x '~~' y" := (bin_rel x y) : rel_scope.
