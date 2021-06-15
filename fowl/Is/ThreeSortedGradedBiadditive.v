(* bad *)
From Maniunfold.Has Require Export
  OneSortedUnaryOperation OneSortedAddition Action
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedGradedMultiplication OneSortedGradedOne
  ThreeSortedGradedBinaryFunction.
From Maniunfold.Is Require Export
  TwoSortedLeftDistributive ThreeSortedBicompatible
  OneSortedCommutativeRing TwoSortedLeftModule TwoSortedRightModule
  TwoSortedGradedLeftModule TwoSortedGradedRightModule
  ThreeSortedGradedBimodule
  TwoSortedGradedBimodule
  TwoSortedUnital Isomorphism
  ThreeSortedGradedLeftBiadditive ThreeSortedGradedRightBiadditive.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations TwoSortedMultiplicativeNotations
  OneSortedGradedArithmeticNotations
  TwoSortedGradedMultiplicativeNotations.

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
