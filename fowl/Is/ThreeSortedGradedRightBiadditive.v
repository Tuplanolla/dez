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
  TwoSortedUnital Isomorphism.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsGrdRBiaddve (A : Type) (P Q R : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (Q i))
  `(forall i : A, HasAdd (R i))
  `(!HasGrdBinFn P Q R bin_op) : Prop :=
  grd_r_biaddve : forall (i j : A) (x : P i) (y z : Q j),
    grd_bin_fn _ _ x (y + z) = grd_bin_fn _ _ x y + grd_bin_fn _ _ x z.
