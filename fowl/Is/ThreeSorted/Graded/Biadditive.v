(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  TwoSorted.Graded.LeftModule TwoSorted.Graded.RightModule
  ThreeSorted.Graded.Bimodule
  TwoSorted.Graded.Bimodule
  TwoSorted.Unital TwoSorted.Isomorphism
  ThreeSorted.Graded.LeftBiadditive ThreeSorted.Graded.RightBiadditive.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations
  OneSorted.Graded.ArithmeticNotations
  TwoSorted.Graded.MultiplicativeNotations.

Class IsGrdBiaddve (A : Type) (P Q R : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(R_has_add : forall i : A, HasAdd (R i))
  `(!HasGrdBinFn P Q R bin_op) : Prop := {
  add_add_grd_bin_fn_is_grd_l_biaddve :>
    @IsGrdLBiaddve A P Q R bin_op null_op P_has_add R_has_add grd_bin_fn;
  add_add_grd_bin_fn_is_grd_r_biaddve :>
    @IsGrdRBiaddve A P Q R bin_op null_op Q_has_add R_has_add grd_bin_fn;
}.
