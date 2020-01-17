From Maniunfold.Has Require Export
  BinaryRelation.

Delimit Scope binary_relation_scope with binary_relation.

Open Scope binary_relation_scope.

Reserved Notation "x '~' y" (at level 70, no associativity).
Notation "x '~' y" := (bi_rel x y) : binary_relation_scope.
