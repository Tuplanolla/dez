From Maniunfold.Has Require Export
  TwoSortedRightAction OneSortedNullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedAdditiveNotations.

Local Open Scope grp_scope.
Local Open Scope r_mod_scope.

(** Unital; left chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsTwoRUnl (A B : Type)
  `(HasRAct A B) `(HasNullOp A) : Prop :=
  two_r_unl : forall x : B, x + 0 = x.
