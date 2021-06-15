(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation OneSortedNullaryOperation
  GradedBinaryOperation OneSortedGradedNullaryOperation
  GradedAction.
From Maniunfold.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedAdditiveNotations
  OneSortedGradedMultiplicativeNotations
  TwoSortedGradedMultiplicativeNotations.

Local Close Scope type_scope.
Local Open Scope grd_r_mod_scope.

Class IsTwoGrdRUnl (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!HasGrdActR P Q bin_op) `(!HasGrdOne P null_op) : Prop := {
  bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
  grd_two_r_unl : forall (i : A) (x : Q i),
    rew r_unl i in (x * 1) = x;
}.
