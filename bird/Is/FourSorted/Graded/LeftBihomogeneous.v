(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation
  TwoSorted.Graded.LeftAction ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  OneSorted.Associative.
From Maniunfold.ShouldHave Require Import
  TwoSorted.Graded.MultiplicativeNotations.

Local Open Scope grd_l_mod_scope.

Class IsGrdLBihomogen {A : Type} (P Q R S : A -> Type)
  {A_has_bin_op : HasBinOp A}
  (P_Q_has_grd_l_act : HasGrdLAct P Q) (P_S_has_grd_l_act : HasGrdLAct P S)
  (Q_R_S_has_grd_bin_fn : HasGrdBinFn Q R S) : Prop := {
  A_bin_op_is_assoc :> IsAssoc A bin_op;
  grd_l_bihomogen : forall {i j k : A} (a : P i) (x : Q j) (y : R k),
    rew assoc i j k in (a * grd_bin_fn _ _ x y) = grd_bin_fn _ _ (a * x) y;
}.
