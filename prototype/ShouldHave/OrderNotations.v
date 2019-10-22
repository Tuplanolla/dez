From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.ShouldHave Require Export
  EquivalenceNotations.

Delimit Scope order_relation_scope with order_relation.

Open Scope order_relation_scope.

Notation "x '<=' y" := (ord x y) : order_relation_scope.
Notation "x '<' y" := (ord x y /\ not (eqv x y)) : order_relation_scope.
