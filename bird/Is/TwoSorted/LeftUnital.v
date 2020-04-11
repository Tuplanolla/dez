From Maniunfold.Has Require Export
  TwoSorted.LeftAction OneSorted.NullaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations TwoSorted.AdditiveNotations.

Local Open Scope l_mod_scope.

(** Unital; left chirality.
    See [Is.OneSorted.LeftUnital]. *)

Class IsTwoLUnl (A B : Type)
  (A_B_has_l_act : HasLAct A B) (A_has_null_op : HasNullOp A) : Prop :=
  two_l_unl : forall x : B, 0 + x = x.
