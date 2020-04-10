From Maniunfold.Has Require Export
  OneSorted.UnaryOperation
  TwoSorted.LeftAction TwoSorted.RightAction
  TwoSorted.LeftTorsion TwoSorted.RightTorsion.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '+' y" (at level 50, left associativity).
Reserved Notation "x '-' y" (at level 50, left associativity).

(** We do not open [l_act_scope] or [r_act_scope],
    because we do not want to favor one over the other.
    The same applies to [l_tor_scope] and [r_tor_scope]. *)

Declare Scope l_act_scope.

Delimit Scope l_act_scope with l_act.

Notation "a '+' x" := (l_act a x) : l_act_scope.
Notation "a '-' x" := (l_act a (un_op x)) : l_act_scope.

Declare Scope r_act_scope.

Delimit Scope r_act_scope with r_act.

Notation "x '+' a" := (r_act x a) : r_act_scope.
Notation "x '-' a" := (r_act x (un_op a)) : r_act_scope.

Declare Scope l_tor_scope.

Delimit Scope l_tor_scope with l_tor.

Notation "x '-' y" := (l_tor x y) : l_tor_scope.

Declare Scope r_tor_scope.

Delimit Scope r_tor_scope with r_tor.

Notation "x '-' y" := (r_tor x y) : r_tor_scope.
