From Maniunfold.Has Require Export
  TwoSorted.RightAction TwoSorted.RightTorsion.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Local Open Scope r_act_scope.

Class IsRUniq (A B : Type)
  (A_B_has_r_act : HasRAct A B) (A_B_has_r_tor : HasRTor A B) : Prop :=
  r_uniq : forall x y : B, x + (y - x)%r_tor = y.
