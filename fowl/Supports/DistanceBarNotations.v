(** * Vertical Bar Notations for Distances *)

From DEZ.Has Require Import
  Distances.

Declare Scope dist_scope.
Delimit Scope dist_scope with dist.

Notation "'|_-_|'" := dist : dist_scope.
Notation "'|' y '-' x '|'" := (dist x y)
  (format "'|' y  '-'  x '|'") : dist_scope.
