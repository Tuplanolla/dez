From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  Addition Zero Negation
  OneSortedGradedMultiplication OneSortedGradedOne
  GradedAction.
From DEZ.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup
  TwoSortedGradedRightLeftDistributive TwoSortedGradedRightCompatible
  TwoSortedGradedRightUnital TwoSortedGradedRightRightDistributive.

(** Graded module over a noncommutative ring; right chirality.
    See [Is.TwoSortedGradedLeftModule]. *)

Class IsGrdRMod (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!@HasGrdMul A P bin_op) `(!@HasGrdOne A P null_op)
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(Q_has_zero : forall i : A, HasZero (Q i))
  `(Q_has_neg : forall i : A, HasNeg (Q i))
  `(!@HasGrdActR A P Q bin_op) : Prop := {
  add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  add_add_grd_act_r_is_grd_two_distr_r :>
    @IsTwoGrdRDistrL A P Q bin_op null_op P_has_add Q_has_add grd_act_r;
  grd_mul_grd_act_r_is_grd_r_compat :>
    @IsGrdRCompat A P Q bin_op null_op grd_mul grd_act_r;
  zero_grd_act_r_is_grd_two_unl_r :>
    @IsTwoGrdUnlR A P Q bin_op null_op grd_act_r grd_one;
  add_grd_act_r_is_grd_two_distr_r :>
    @IsTwoGrdRDistrR A P Q bin_op null_op Q_has_add grd_act_r;
}.
