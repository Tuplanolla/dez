From Maniunfold.Has Require Export
  OneSortedApartnessRelation.

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Reserved Notation "x '##' y" (no associativity, at level 70).

Notation "x '##' y" := (apart_rel x y) : rel_scope.

Notation "'_##_'" := apart_rel (only parsing) : rel_scope.
