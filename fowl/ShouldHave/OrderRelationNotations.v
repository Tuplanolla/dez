From Maniunfold.Has Require Export
  OrderRelation.

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

Notation "'_<=_'" := ord_rel : rel.
Notation "x '<=' y" := (ord_rel x y) : rel.

#[global] Open Scope rel.
