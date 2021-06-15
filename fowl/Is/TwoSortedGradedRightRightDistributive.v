(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation
  GradedAction.
From Maniunfold.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedAdditiveNotations
  OneSortedGradedMultiplicativeNotations
  TwoSortedGradedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope grd_r_mod_scope.

Class IsTwoGrdRRDistr (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (Q i))
  `(!HasGrdActR P Q bin_op) : Prop :=
  grd_two_r_r_distr : forall (i j : A) (x y : Q i) (a : P j),
    (x + y) * a = x * a + y * a.
