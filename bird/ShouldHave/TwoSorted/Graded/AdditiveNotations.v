(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.Graded.LeftAction.

(** TODO More from [ShouldHave.TwoSorted.AdditiveNotations]. *)

Declare Scope action_scope.

Delimit Scope action_scope with action.

Open Scope action_scope.

Reserved Notation "a 'GL+' x" (at level 50, left associativity).

Notation "a 'GL+' x" := (grd_l_act _ _ a x) : action_scope.
