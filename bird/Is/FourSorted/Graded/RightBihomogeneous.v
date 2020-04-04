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
  TwoSorted.Unital TwoSorted.Isomorphism.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations
  OneSorted.Graded.ArithmeticNotations
  TwoSorted.Graded.MultiplicativeNotations.

Class IsGrdRBihomogen {A : Type} (P Q R S : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_R_has_grd_r_act : HasGrdRAct P R) (P_S_has_grd_r_act : HasGrdRAct P S)
  (Q_R_S_has_grd_bin_fn : HasGrdBinFn Q R S) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  grd_r_bihomogen : forall {i j k : A} (x : Q i) (y : R j) (a : P k),
    rew assoc i j k in (grd_bin_fn _ _ x (y GR* a)) = grd_bin_fn _ _ x y GR* a;
}.
