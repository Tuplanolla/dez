From Maniunfold.Has Require Export
  Addition Zero Negation
  OneSortedGradedMultiplication OneSortedGradedOne
  GradedAction GradedAction.
From Maniunfold.Is Require Export
  FiveSortedGradedBilinearMapping.

(** Graded bilinear operator
    on a graded bimodule over a graded noncommutative ring.
    The grading is carried by [A], the ring by [P] and the bimodule by [Q].
    See [Is.TwoSortedBilinearOperator]. *)

Class IsGrdBilinOp (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!HasGrdMul P bin_op) `(!HasGrdOne P null_op)
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(Q_has_zero : forall i : A, HasZero (Q i))
  `(Q_has_neg : forall i : A, HasNeg (Q i))
  `(!HasGrdActL P Q bin_op) `(!HasGrdActR P Q bin_op)
  `(!HasGrdMul Q bin_op) : Prop :=
  P_P_Q_Q_Q_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_mul_grd_one_add_zero_neg_add_zero_neg_add_zero_neg_grd_act_l_grd_act_r_grd_act_l_grd_act_r_grd_mul_is_bilin_map
    :> @IsGrdBilinMap A P P Q Q Q bin_op null_op
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg
    Q_has_add Q_has_zero Q_has_neg
    Q_has_add Q_has_zero Q_has_neg
    grd_act_l grd_act_r grd_act_l grd_act_r grd_mul.
