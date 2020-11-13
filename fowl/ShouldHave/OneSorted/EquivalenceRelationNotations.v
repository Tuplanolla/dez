From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation.

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Notation "x '==' y" := (eq_rel x y) : rel_scope.

Notation "'_==_'" := eq_rel (only parsing) : rel_scope.
