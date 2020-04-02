From Maniunfold.Has Require Export
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction.

(** TODO More from [ShouldHave.TwoSorted.MultiplicativeNotations]. *)

Declare Scope action_scope.

Delimit Scope action_scope with action.

Open Scope action_scope.

Reserved Notation "a 'GL*' x" (at level 40, left associativity).
Reserved Notation "x 'GR*' a" (at level 40, left associativity).

Notation "a 'GL*' x" := (grd_l_act _ _ a x) : action_scope.
Notation "x 'GR*' a" := (grd_r_act _ _ x a) : action_scope.
