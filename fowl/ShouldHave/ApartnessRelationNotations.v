(** * Notations for Apartness Relations *)

From Maniunfold.Has Require Import
  ApartnessRelation.

Reserved Notation "x '#' y" (no associativity, at level 70).

Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

#[global] Open Scope relation_scope.

Notation "'_#_'" := apart_rel : relation_scope.
Notation "x '#' y" := (apart_rel x y) : relation_scope.
