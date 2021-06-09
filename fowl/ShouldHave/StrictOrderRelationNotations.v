From Maniunfold.Has Require Export
  StrictOrderRelation.

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Notation "'_<_'" := str_ord_rel : rel_scope.
Notation "x '<' y" := (str_ord_rel x y) : rel_scope.
