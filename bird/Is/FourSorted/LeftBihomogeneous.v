(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction ThreeSorted.BinaryFunction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLBihomogen (A B C D : Type)
  (A_B_has_l_act : HasLAct A B) (A_D_has_l_act : HasLAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  l_bihomogen : forall (a : A) (x : B) (y : C),
    a * bin_fn x y = bin_fn (a * x) y.
