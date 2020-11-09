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
  TwoSorted.Unital TwoSorted.Isomorphism.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsGrdLBiaddve (A : Type) (P Q R : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (P i))
  `(forall i : A, HasAdd (R i))
  `(HasGrdBinFn A P Q R) : Prop :=
  grd_l_biaddve : forall (i j : A) (x y : P i) (z : Q j),
    grd_bin_fn _ _ (x + y) z = grd_bin_fn _ _ x z + grd_bin_fn _ _ y z.
