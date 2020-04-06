(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction
  OneSorted.LeftNullaryOperation OneSorted.RightNullaryOperation
  OneSorted.LeftUnaryOperation OneSorted.RightUnaryOperation
  TwoSorted.LeftTorsion TwoSorted.RightTorsion.

Declare Scope action_scope.

Delimit Scope action_scope with action.

Open Scope action_scope.

(** The suffix notation [0L] would cause a syntax error at a later point,
    which is why we adopt the prefix notation convention instead. *)

Reserved Notation "a 'L+' x" (at level 50, left associativity).
Reserved Notation "x 'R+' a" (at level 50, left associativity).
Reserved Notation "'L0'" (at level 0, no associativity).
Reserved Notation "'R0'" (at level 0, no associativity).
Reserved Notation "'L-' x" (at level 35, right associativity).
Reserved Notation "'R-' x" (at level 35, right associativity).
Reserved Notation "x 'L-' y" (at level 50, left associativity).
Reserved Notation "x 'R-' y" (at level 50, left associativity).

Notation "a 'L+' x" := (l_act a x) : action_scope.
Notation "x 'R+' a" := (r_act x a) : action_scope.
Notation "'L0'" := l_null_op : action_scope.
Notation "'R0'" := r_null_op : action_scope.
Notation "'L-' x" := (l_un_op x) : action_scope.
Notation "'R-' x" := (r_un_op x) : action_scope.
Notation "x 'L-' y" := (l_tor x y) : action_scope.
Notation "x 'R-' y" := (r_tor x y) : action_scope.
