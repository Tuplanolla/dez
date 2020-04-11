(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.RightAction TwoSorted.Function.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRHomogen (A B C : Type)
  (A_B_has_r_act : HasRAct A B) (A_C_has_r_act : HasRAct A C)
  (B_C_has_fn : HasFn B C) : Prop :=
  r_homogen : forall (a : A) (x : B), fn (x * a) = fn x * a.
