(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Declare Scope relation_scope.

Delimit Scope relation_scope with relation.

Open Scope relation_scope.

Reserved Notation "x '~~' y" (at level 70, no associativity).
Reserved Notation "x '~/~' y" (at level 70, no associativity).

Notation "x '~~' y" := (bin_rel x y) : relation_scope.
Notation "x '~/~' y" := (not (bin_rel x y)) : relation_scope.
