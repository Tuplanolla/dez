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

Local Open Scope grd_l_mod_scope.

Class IsGrdLCompat (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!@HasGrdMul A P bin_op)
  `(!@HasGrdActL A P Q bin_op) : Prop := {
  A_bin_op_is_assoc :> IsAssoc bin_op;
  grd_l_compat : forall (i j k : A) (a : P i) (b : P j) (x : Q k),
    rew assoc i j k in (a * (b * x)) = (a * b) * x;
}.
