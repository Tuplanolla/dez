From Maniunfold.Has Require Export
  Morphism.

Declare Scope category_scope.
Delimit Scope category_scope with cat.

Notation "'_-->_'" := hom : cat.
Notation "x '-->' y" := (hom x y) : cat.

#[global] Open Scope cat.
