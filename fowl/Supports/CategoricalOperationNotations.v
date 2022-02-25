(** * Notations for Categorical Operations *)

From DEZ.Has Require Import
  CategoricalOperations.
From DEZ.Supports Require Export
  CategoricalRelationNotations.

Notation "'id'" := (id_hom _) : category_scope.
Notation "'_^-1'" := (inv_hom _ _) : category_scope.
Notation "f '^-1'" := (inv_hom _ _ f) : category_scope.
Notation "'_o_'" := (comp_hom _ _ _) : category_scope.
Notation "g 'o' f" := (comp_hom _ _ _ g f) : category_scope.
