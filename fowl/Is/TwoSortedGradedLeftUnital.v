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

Local Open Scope grd_grp_scope.
Local Open Scope grd_l_mod_scope.

Class IsTwoGrdUnlL (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!HasGrdActL P Q bin_op) `(!HasGrdOne P null_op) : Prop := {
  bin_op_null_op_is_unl_l :> IsUnlBinOpL null_op bin_op;
  grd_two_unl_l : forall (i : A) (x : Q i),
    rew unl_bin_op_l i in (1 * x) = x;
}.
