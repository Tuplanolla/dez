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

Local Open Scope grd_r_mod_scope.

Class IsGrdRCompat (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!@HasGrdMul A P bin_op)
  `(!@HasGrdActR A P Q bin_op) : Prop := {
  A_bin_op_is_assoc :> IsAssoc bin_op;
  grd_r_compat : forall (i j k : A) (x : Q i) (a : P j) (b : P k),
    rew assoc i j k in (x * (a * b)) = (x * a) * b;
}.
