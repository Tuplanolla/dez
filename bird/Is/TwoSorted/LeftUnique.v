(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.LeftTorsion.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Local Open Scope l_act_scope.

Class IsLUniq (A B : Type)
  (A_B_has_l_act : HasLAct A B) (A_B_has_l_tor : HasLTor A B) : Prop :=
  l_uniq : forall x y : B, (y - x)%l_tor + x = y.
