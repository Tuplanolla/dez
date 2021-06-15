From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedGradedMultiplication OneSortedGradedOne
  GradedAction GradedAction
  ThreeSortedGradedBinaryFunction.
From Maniunfold.Is Require Export
  TwoSortedGradedLeftModule TwoSortedGradedRightModule
  ThreeSortedGradedBimodule
  ThreeSortedGradedBiadditive FiveSortedGradedBihomogeneous.

(** Graded bilinear mapping
    from a graded left module and a graded right module into a graded bimodule,
    where each module is defined over a graded noncommutative ring.
    The grading is carried by [A], the rings by [P] and [Q],
    the left module by [R], the right module by [S] and the bimodule by [T].
    See [Is.FiveSortedBilinearMapping]. *)

Class IsGrdBilinMap (A : Type) (P Q R S T : A -> Type)
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
  `(S_has_add : forall i : A, HasAdd (S i))
  `(S_has_zero : forall i : A, HasZero (S i))
  `(S_has_neg : forall i : A, HasNeg (S i))
  `(T_has_add : forall i : A, HasAdd (T i))
  `(T_has_zero : forall i : A, HasZero (T i))
  `(T_has_neg : forall i : A, HasNeg (T i))
  `(!HasGrdActL P R bin_op) `(!HasGrdActR Q S bin_op)
  `(!HasGrdActL P T bin_op) `(!HasGrdActR Q T bin_op)
  `(!HasGrdBinFn R S T bin_op) : Prop := {
  P_R_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_act_l_is_grd_l_mod :>
    @IsGrdLMod A P R bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_act_l;
  Q_S_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_act_r_is_grd_r_mod :>
    @IsGrdRMod A Q S bin_op null_op Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    S_has_add S_has_zero S_has_neg grd_act_r;
  P_Q_T_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_act_l_grd_act_r_is_three_grd_bimod
    :> @IsThreeGrdBimod A P Q T bin_op null_op
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    T_has_add T_has_zero T_has_neg grd_act_l grd_act_r;
  R_S_T_add_add_add_grd_bin_fn_is_grd_biaddve :>
    @IsGrdBiaddve A R S T bin_op null_op R_has_add S_has_add T_has_add grd_bin_fn;
  P_Q_R_S_T_grd_act_l_grd_act_r_grd_act_l_grd_act_r_grd_bin_fn_is_grd_bihomogen
    :> @IsGrdBihomogen A P Q R S T bin_op null_op
    grd_act_l grd_act_r grd_act_l grd_act_r grd_bin_fn;
}.
