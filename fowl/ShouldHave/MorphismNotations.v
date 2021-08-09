(** * Notations for Categories *)

From DEZ.Has Require Import
  Morphism.

Declare Scope category_scope.
Delimit Scope category_scope with cat.

#[global] Open Scope category_scope.

Notation "'_-->_'" := hom : category_scope.
Notation "x '-->' y" := (hom x y) : category_scope.
