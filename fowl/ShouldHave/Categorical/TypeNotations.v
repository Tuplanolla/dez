From Maniunfold.Has Require Export
  Categorical.Morphism.

Reserved Notation "x '-->' y"
  (at level 99, right associativity, y at level 200).

Declare Scope cat_scope.

Delimit Scope cat_scope with cat.

Open Scope cat_scope.

Notation "x '-->' y" := (hom x y) : cat_scope.
