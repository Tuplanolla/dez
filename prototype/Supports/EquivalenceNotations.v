From Maniunfold.Has Require Export
  EquivalenceRelation.

Delimit Scope equivalence_relation_scope with equivalence_relation.

Open Scope equivalence_relation_scope.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y) : equivalence_relation_scope.

Reserved Notation "x '=/=' y" (at level 70, no associativity).
Notation "x '=/=' y" := (not (eqv x y)) : equivalence_relation_scope.
