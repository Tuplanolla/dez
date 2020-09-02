(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation
  TwoSorted.Graded.RightAction ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  OneSorted.Associative.
From Maniunfold.ShouldHave Require Import
  TwoSorted.Graded.MultiplicativeNotations.

Local Open Scope grd_r_mod_scope.

Class IsGrdRBihomogen {A : Type} (P Q R S : A -> Type)
  {A_has_bin_op : HasBinOp A}
  (P_R_has_grd_r_act : HasGrdRAct P R) (P_S_has_grd_r_act : HasGrdRAct P S)
  (Q_R_S_has_grd_bin_fn : HasGrdBinFn Q R S) : Prop := {
  A_bin_op_is_assoc :> IsAssoc A bin_op;
  grd_r_bihomogen : forall {i j k : A} (x : Q i) (y : R j) (a : P k),
    rew assoc i j k in (grd_bin_fn _ _ x (y * a)) = grd_bin_fn _ _ x y * a;
}.
