From Maniunfold.Has Require Export
  EquivalenceRelation.

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

Notation "'_==_'" := eq_rel : rel.
Notation "x '==' y" := (eq_rel x y) : rel.

#[global] Open Scope rel.
