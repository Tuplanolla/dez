(* bad *)
From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  GradedBinaryOperation GradedNullaryOperation
  GradedAction.
From DEZ.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedAdditiveNotations
  OneSortedGradedMultiplicativeNotations
  TwoSortedGradedMultiplicativeNotations.

Local Open Scope ring_scope.
Local Open Scope grd_l_mod_scope.

Class IsTwoGrdLDistrR (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (P i))
  `(forall i : A, HasAdd (Q i))
  `(!HasGrdActL P Q bin_op) : Prop :=
  grd_two_l_distr_r : forall (i j : A) (a b : P i) (x : Q j),
    (a + b) * x = a * x + b * x.
