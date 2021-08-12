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

Local Open Scope grd_grp_scope.
Local Open Scope grd_r_mod_scope.

Class IsTwoGrdUnlR (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!HasGrdActR P Q bin_op) `(!HasGrdOne P null_op) : Prop := {
  bin_op_null_op_is_unl_r :> IsUnlR null_op bin_op;
  grd_two_unl_r : forall (i : A) (x : Q i),
    rew unl_r i in (x * 1) = x;
}.
