(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  TwoSorted.Graded.LeftModule TwoSorted.Graded.RightModule
  ThreeSorted.Graded.Bimodule
  TwoSorted.Graded.Bimodule
  TwoSorted.Unital TwoSorted.Isomorphism
  FourSorted.Graded.LeftBihomogeneous FourSorted.Graded.RightBihomogeneous.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations
  OneSorted.Graded.ArithmeticNotations
  TwoSorted.Graded.MultiplicativeNotations.

Class IsGrdBihomogen {A : Type} (P Q R S T : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_R_has_grd_l_act : HasGrdLAct P R) (Q_S_has_grd_r_act : HasGrdRAct Q S)
  (P_T_has_grd_l_act : HasGrdLAct P T) (Q_T_has_grd_r_act : HasGrdRAct Q T)
  (R_S_T_has_grd_bin_fn : HasGrdBinFn R S T) : Prop := {
  P_R_S_T_grd_l_act_grd_l_act_grd_bin_fn_is_grd_l_bihomogen :>
    IsGrdLBihomogen P R S T grd_l_act grd_l_act grd_bin_fn;
  Q_R_S_T_grd_r_act_grd_r_act_grd_bin_fn_is_grd_r_bihomogen :>
    IsGrdRBihomogen Q R S T grd_r_act grd_r_act grd_bin_fn;
}.
