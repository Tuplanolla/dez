From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction
  TwoSorted.LeftTorsion TwoSorted.RightTorsion.

Declare Scope action_scope.

Delimit Scope action_scope with action.

Open Scope action_scope.

(** See [ShouldHave.TwoSorted.AdditiveNotations]. *)

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
Notation "x 'L/' y" := (l_tor x y) : action_scope.
Notation "x 'R/' y" := (r_tor x y) : action_scope.
