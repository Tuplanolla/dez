(** * Notations for Equivalence Relations *)

From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.ShouldHave Require Export
  BinaryRelationNotations.

Notation "'_==_'" := eq_rel : relation_scope.
Notation "x '==' y" := (eq_rel x y) : relation_scope.
