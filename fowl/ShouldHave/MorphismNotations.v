(** * Notations for Categories *)

From Maniunfold.Has Require Export
  Morphism.

Declare Scope category_scope.
Delimit Scope category_scope with cat.

#[global] Open Scope category_scope.

Notation "'_-->_'" := hom : category_scope.
Notation "x '-->' y" := (hom x y) : category_scope.
