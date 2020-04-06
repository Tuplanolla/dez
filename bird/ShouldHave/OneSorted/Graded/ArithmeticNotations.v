(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Graded.Addition OneSorted.Graded.Zero (*OneSorted.Graded.Negation*)
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  (*OneSorted.Graded.Reciprocation*).

Declare Scope ring_scope.

Delimit Scope ring_scope with ring.

Open Scope ring_scope.

Reserved Notation "x 'G+' y" (at level 50, left associativity).
Reserved Notation "'G0'" (at level 0, no associativity).
Reserved Notation "'G-' x" (at level 35, right associativity).
Reserved Notation "x 'G*' y" (at level 40, left associativity).
Reserved Notation "'G1'" (at level 0, no associativity).
Reserved Notation "'G/' x" (at level 35, right associativity).

Notation "x 'G+' y" := (grd_add _ _ x y) : ring_scope.
Notation "'G0'" := grd_zero : ring_scope.
(*Notation "'G-' x" := (grd_neg _ x) : ring_scope.*)
Notation "x 'G*' y" := (grd_mul _ _ x y) : ring_scope.
Notation "'G1'" := grd_one : ring_scope.
(*Notation "'G/' x" := (grd_recip _ x) : ring_scope.*)
