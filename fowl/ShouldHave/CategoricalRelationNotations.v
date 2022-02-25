(** * Notations for Categorical Relations *)

From DEZ.Has Require Export
  CategoricalRelations.

Declare Scope category_scope.
Delimit Scope category_scope with cat.

#[export] Open Scope category_scope.

Notation "'_-->_'" := hom : category_scope.
Notation "x '-->' y" := (hom x y) : category_scope.
