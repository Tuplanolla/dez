(** * Notations for Equivalence Relations *)

From DEZ.Has Require Import
  EquivalenceRelation.

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

#[global] Open Scope relation_scope.

Notation "'_==_'" := eq_rel : relation_scope.
Notation "x '==' y" := (eq_rel x y) : relation_scope.
