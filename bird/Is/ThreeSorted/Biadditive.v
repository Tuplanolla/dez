(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  ThreeSorted.Bimodule
  TwoSorted.Unital TwoSorted.Isomorphism
  ThreeSorted.LeftBiadditive ThreeSorted.RightBiadditive.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

Class IsBiaddve (A B C : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop := {
  A_B_C_add_add_bin_fn_is_l_biaddve :> IsLBiaddve A B C add add bin_fn;
  A_B_C_add_add_bin_fn_is_r_biaddve :> IsRBiaddve A B C add add bin_fn;
}.
