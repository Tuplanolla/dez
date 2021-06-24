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

Local Open Scope ring_scope.
Local Open Scope grd_l_mod_scope.

Class IsTwoGrdLDistrL (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (Q i))
  `(!HasGrdActL P Q bin_op) : Prop :=
  grd_two_l_distr_l : forall (i j : A) (a : P i) (x y : Q j),
    a * (x + y) = a * x + a * y.
