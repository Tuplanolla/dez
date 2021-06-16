From Maniunfold.Has Require Export
  OrderRelations.

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

Notation "'_<=_'" := ord_rel : rel.
Notation "x '<=' y" := (ord_rel x y) : rel.
Notation "'_<_'" := str_ord_rel : rel.
Notation "x '<' y" := (str_ord_rel x y) : rel.

#[global] Open Scope rel.
