From Maniunfold.Has Require Export
  TwoSortedLeftAction OneSortedNullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations TwoSortedAdditiveNotations.

Local Open Scope grp_scope.
Local Open Scope l_mod_scope.

(** Unital; left chirality.
    See [Is.OneSortedLeftUnital]. *)

Class IsTwoLUnl (A B : Type)
  `(HasLAct A B) `(HasNullOp A) : Prop :=
  two_l_unl : forall x : B, 0 + x = x.
