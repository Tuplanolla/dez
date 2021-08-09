(* bad *)
From DEZ.Has Require Export
  BinaryOperation
  GradedAction ThreeSortedGradedBinaryFunction.
From DEZ.Is Require Export
  Associative.
From DEZ.ShouldHave Require Import
  TwoSortedGradedMultiplicativeNotations.

Local Open Scope grd_r_mod_scope.

Class IsGrdRBihomogen (A : Type) (P Q R S : A -> Type) `(HasBinOp A)
  `(!@HasGrdActR A P R bin_op) `(!@HasGrdActR A P S bin_op)
  `(!@HasGrdBinFn A Q R S bin_op) : Prop := {
  A_bin_op_is_assoc :> IsAssoc bin_op;
  grd_r_bihomogen : forall (i j k : A) (x : Q i) (y : R j) (a : P k),
    rew assoc i j k in (grd_bin_fn _ _ x (y * a)) = grd_bin_fn _ _ x y * a;
}.
