(** * Notations for Order Relations *)

From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.ShouldHave Require Export
  BinaryRelationNotations.

Notation "'_<=_'" := ord_rel : relation_scope.
Notation "x '<=' y" := (ord_rel x y) : relation_scope.
Notation "'_<_'" := str_ord_rel : relation_scope.
Notation "x '<' y" := (str_ord_rel x y) : relation_scope.
