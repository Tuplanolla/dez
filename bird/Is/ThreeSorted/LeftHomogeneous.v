(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.Function.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLHomogen (A B C : Type)
  (A_B_has_l_act : HasLAct A B) (A_C_has_l_act : HasLAct A C)
  (B_C_has_fn : HasFn B C) : Prop :=
  l_homogen : forall (a : A) (x : B), fn (a * x) = a * fn x.
