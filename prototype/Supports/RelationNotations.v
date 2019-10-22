From Maniunfold.Has Require Export
  Relation.

Delimit Scope relation_scope with relation.

Open Scope relation_scope.

Reserved Notation "x '~' y" (at level 70, no associativity).
Notation "x '~' y" := (rel x y) : relation_scope.
