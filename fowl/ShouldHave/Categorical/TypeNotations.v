From Maniunfold.Has Require Export
  Categorical.Morphism.

Declare Scope cat_scope.

Delimit Scope cat_scope with cat.

Open Scope cat_scope.

Notation "x '-->' y" := (hom x y) : cat_scope.

Notation "'_-->_'" := hom (only parsing) : cat_scope.
