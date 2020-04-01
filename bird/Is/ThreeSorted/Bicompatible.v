From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Class IsBicompat (A B C : Type)
  (A_C_has_l_act : HasLAct A C) (B_C_has_r_act : HasRAct B C) : Prop :=
  bicompat : forall (a : A) (x : C) (b : B), a L+ (x R+ b) = (a L+ x) R+ b.
