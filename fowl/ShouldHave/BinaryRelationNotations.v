From Maniunfold.Has Require Export
  BinaryRelation.

Reserved Notation "x '~~' y" (no associativity, at level 70).

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

Notation "'_~~_'" := bin_rel : rel.
Notation "x '~~' y" := (bin_rel x y) : rel.

#[global] Open Scope rel.
