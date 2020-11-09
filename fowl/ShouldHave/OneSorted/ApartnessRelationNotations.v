(* bad *)
From Maniunfold.Has Require Export
  OneSorted.ApartnessRelation.

Reserved Notation "x '##' y" (at level 70, no associativity).
Reserved Notation "x '#/#' y" (at level 70, no associativity).

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Notation "x '##' y" := (apart_rel x y) : rel_scope.
Notation "x '#/#' y" := (not (apart_rel x y)) : rel_scope.
