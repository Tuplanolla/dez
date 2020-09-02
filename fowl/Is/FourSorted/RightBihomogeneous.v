(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.RightAction ThreeSorted.BinaryFunction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRBihomogen (A B C D : Type)
  (A_C_has_r_act : HasRAct A C) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  r_bihomogen : forall (x : B) (y : C) (a : A),
    bin_fn x (y * a) = bin_fn x y * a.
