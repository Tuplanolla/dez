From Maniunfold.Has Require Export
  OneSortedOrderRelation.

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Notation "'_<=_'" := ord_rel : rel_scope.
Notation "x '<=' y" := (ord_rel x y) : rel_scope.
