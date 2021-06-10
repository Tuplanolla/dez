(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation
  OneSortedGradedBinaryOperation OneSortedGradedNullaryOperation
  TwoSortedGradedLeftAction.
From Maniunfold.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedAdditiveNotations
  OneSortedGradedMultiplicativeNotations
  TwoSortedGradedMultiplicativeNotations.

Local Open Scope grp_scope.
Local Open Scope grd_l_mod_scope.

Class IsTwoGrdLLDistr (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (Q i))
  `(!HasGrdLAct P Q bin_op) : Prop :=
  grd_two_l_l_distr : forall (i j : A) (a : P i) (x y : Q j),
    a * (x + y) = a * x + a * y.
