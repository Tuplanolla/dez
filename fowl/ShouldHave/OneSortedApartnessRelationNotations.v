From Maniunfold.Has Require Export
  ApartnessRelation.
From Maniunfold.ShouldHave Require Export
  BinaryRelationNotations.

Reserved Notation "x '#' y" (no associativity, at level 70).

Notation "'_#_'" := apart_rel : relation_scope.
Notation "x '#' y" := (apart_rel x y) : relation_scope.
