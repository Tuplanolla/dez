From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction
  OneSorted.LeftNullaryOperation OneSorted.RightNullaryOperation
  OneSorted.LeftUnaryOperation OneSorted.RightUnaryOperation
  TwoSorted.LeftTorsion TwoSorted.RightTorsion.

Declare Scope action_scope.

Delimit Scope action_scope with action.

Open Scope action_scope.

(** Trying to use [1L] would cause a syntax error later,
    which is why we adopt the prefix convention instead. *)

Reserved Notation "a 'L*' x" (at level 40, left associativity).
Reserved Notation "x 'R*' a" (at level 40, left associativity).
Reserved Notation "'L1'" (at level 0, no associativity).
Reserved Notation "'R1'" (at level 0, no associativity).
Reserved Notation "'L/' x" (at level 35, right associativity).
Reserved Notation "'R/' x" (at level 35, right associativity).
Reserved Notation "x 'L/' y" (at level 40, left associativity).
Reserved Notation "x 'R/' y" (at level 40, left associativity).

Notation "a 'L*' x" := (l_act a x) : action_scope.
Notation "x 'R*' a" := (r_act x a) : action_scope.
Notation "'L1'" := l_null_op : action_scope.
Notation "'R1'" := r_null_op : action_scope.
Notation "'L/' x" := (l_un_op x) : action_scope.
Notation "'R/' x" := (r_un_op x) : action_scope.
Notation "x 'L/' y" := (l_tor x y) : action_scope.
Notation "x 'R/' y" := (r_tor x y) : action_scope.
