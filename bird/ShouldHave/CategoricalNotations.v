From Maniunfold.Has Require Export
  Morphism.

Declare Scope category_scope.

Delimit Scope category_scope with category.

Open Scope category_scope.

Reserved Notation "x '~>' y" (at level 99, right associativity,
  y at level 200).

Notation "x '~>' y" := (hom x y) : category_scope.
