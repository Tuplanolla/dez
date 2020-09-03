From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Class IsBicompat (A B C : Type)
  (A_C_has_l_act : HasLAct A C) (B_C_has_r_act : HasRAct B C) : Prop :=
  bicompat : forall (a : A) (x : C) (b : B),
    (a * (x * b)%r_mod)%l_mod = ((a * x)%l_mod * b)%r_mod.