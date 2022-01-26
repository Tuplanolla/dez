(** * Notations for Equivalence Relations *)

From DEZ.Has Require Import
  EquivalenceRelation.
From DEZ.Is Require Import
  Reflexive Symmetric Transitive.

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

#[global] Open Scope relation_scope.

Notation "'_==_'" := eq_rel : relation_scope.
Notation "x '==' y" := (eq_rel x y) : relation_scope.

Notation "'id'" := refl : relation_scope.
Notation "'_^-1'" := (sym _ _) : relation_scope.
Notation "a '^-1'" := (sym _ _ a) : relation_scope.
Notation "'_o_'" := (trans _ _ _) : relation_scope.
Notation "b 'o' a" := (trans _ _ _ a b) : relation_scope.
