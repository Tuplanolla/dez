(* bad *)
From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation OneSortedMultiplication
  OneSortedOne Action Action.
From Maniunfold.Is Require Export
  TwoSortedGradedLeftModule TwoSortedGradedRightModule
  ThreeSortedBicompatible.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedAdditiveNotations
  OneSortedGradedMultiplicativeNotations
  TwoSortedGradedMultiplicativeNotations.

Class IsGrdBicompat (A : Type) (P Q R : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!HasGrdActL P R bin_op) `(!HasGrdActR Q R bin_op) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  grd_bicompat : forall (i j k : A) (a : P i) (x : R j) (b : Q k),
    rew assoc i j k in
    (a * (x * b)%grd_r_mod)%grd_l_mod = ((a * x)%grd_l_mod * b)%grd_r_mod;
}.

Class IsThreeGrdBimod (A : Type) (P Q R : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!HasGrdMul P bin_op) `(!HasGrdOne P null_op)
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(Q_has_zero : forall i : A, HasZero (Q i))
  `(Q_has_neg : forall i : A, HasNeg (Q i))
  `(!HasGrdMul Q bin_op) `(!HasGrdOne Q null_op)
  `(R_has_add : forall i : A, HasAdd (R i))
  `(R_has_zero : forall i : A, HasZero (R i))
  `(R_has_neg : forall i : A, HasNeg (R i))
  `(!HasGrdActL P R bin_op) `(!HasGrdActR Q R bin_op) : Prop := {
  add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_act_l_is_grd_l_mod :>
    @IsGrdLMod A P R bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_act_l;
  add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_act_r_is_grd_r_mod :>
    @IsGrdRMod A Q R bin_op null_op Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_act_r;
  grd_act_l_grd_act_r_is_grd_bicompat :>
    @IsGrdBicompat A P Q R bin_op null_op grd_act_l grd_act_r;
}.
