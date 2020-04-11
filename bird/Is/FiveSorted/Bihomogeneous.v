(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  ThreeSorted.Bimodule
  TwoSorted.Unital TwoSorted.Isomorphism
  FourSorted.LeftBihomogeneous FourSorted.RightBihomogeneous.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

Class IsBihomogen (A B C D E : Type)
  (A_C_has_l_act : HasLAct A C) (B_D_has_r_act : HasRAct B D)
  (A_E_has_l_act : HasLAct A E) (B_E_has_r_act : HasRAct B E)
  (C_D_E_has_bin_fn : HasBinFn C D E) : Prop := {
  A_C_D_E_l_act_l_act_bin_fn_is_l_bihomogen :>
    IsLBihomogen A C D E l_act l_act bin_fn;
  B_C_D_E_r_act_r_act_bin_fn_is_r_bihomogen :>
    IsRBihomogen B C D E r_act r_act bin_fn;
}.
