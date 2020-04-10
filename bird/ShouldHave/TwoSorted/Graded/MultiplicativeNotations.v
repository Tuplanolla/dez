From Maniunfold.Has Require Export
  OneSorted.Graded.UnaryOperation
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).

(** We do not open [grd_l_act_scope] or [grd_r_act_scope],
    because we do not want to favor one over the other. *)

Declare Scope grd_l_act_scope.

Delimit Scope grd_l_act_scope with grd_l_act.

Notation "a '*' x" := (grd_l_act _ _ a x) : grd_l_act_scope.
Notation "a '/' x" := (grd_l_act _ _ a (grd_un_op _ x)) : grd_l_act_scope.

Declare Scope grd_r_act_scope.

Delimit Scope grd_r_act_scope with grd_r_act.

Notation "x '*' a" := (grd_r_act _ _ x a) : grd_r_act_scope.
Notation "x '/' a" := (grd_r_act _ _ x (grd_un_op _ a)) : grd_r_act_scope.
