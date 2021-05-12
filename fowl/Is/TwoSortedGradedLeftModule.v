From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedGradedMultiplication OneSortedGradedOne
  TwoSortedGradedLeftAction.
From Maniunfold.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup
  TwoSortedGradedLeftRightDistributive TwoSortedGradedLeftCompatible
  TwoSortedGradedLeftUnital TwoSortedGradedLeftLeftDistributive.

(** Graded module over a noncommutative ring; left chirality.
    The grading is carried by [A], the ring by [P] and the module by [Q]. *)

Class IsGrdLMod (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!@HasGrdMul A P bin_op) `(!@HasGrdOne A P null_op)
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(Q_has_zero : forall i : A, HasZero (Q i))
  `(Q_has_neg : forall i : A, HasNeg (Q i))
  `(!@HasGrdLAct A P Q bin_op) : Prop := {
  add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  add_add_grd_l_act_is_grd_two_r_distr :>
    @IsTwoGrdLRDistr A P Q bin_op null_op P_has_add Q_has_add grd_l_act;
  grd_mul_grd_l_act_is_grd_l_compat :>
    @IsGrdLCompat A P Q bin_op null_op grd_mul grd_l_act;
  zero_grd_l_act_is_grd_two_l_unl :>
    @IsTwoGrdLUnl A P Q bin_op null_op grd_l_act grd_one;
  add_grd_l_act_is_grd_two_l_distr :>
    @IsTwoGrdLLDistr A P Q bin_op null_op Q_has_add grd_l_act;
}.
