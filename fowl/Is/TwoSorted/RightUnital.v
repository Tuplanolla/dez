From Maniunfold.Has Require Export
  TwoSorted.RightAction OneSorted.NullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.AdditiveNotations.

Local Open Scope r_mod_scope.

(** Unital; left chirality.
    See [Is.OneSorted.LeftUnital]. *)

Class IsTwoRUnl (A B : Type)
  (A_B_has_r_act : HasRAct A B) (A_has_null_op : HasNullOp A) : Prop :=
  two_r_unl : forall x : B, x + 0 = x.
