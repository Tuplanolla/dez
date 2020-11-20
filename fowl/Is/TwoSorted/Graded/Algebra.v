From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Graded.Ring
  TwoSorted.Graded.Bimodule TwoSorted.Graded.BilinearOperator.

(** Graded noncommutative nonunital nonassociative algebra
    over a graded noncommutative ring.
    The grading is carried by [A], the ring by [P] and the algebra by [Q].
    See [Is.TwoSorted.Algebra]. *)

Class IsGrdAlg (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!HasGrdMul P bin_op) `(!HasGrdOne P null_op)
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(Q_has_zero : forall i : A, HasZero (Q i))
  `(Q_has_neg : forall i : A, HasNeg (Q i))
  `(!HasGrdMul Q bin_op)
  `(!HasGrdLAct P Q bin_op)
  `(!HasGrdRAct P Q bin_op) : Prop := {
  P_add_zero_neg_grd_mul_grd_one_is_grd_ring :>
    @IsGrdRing A P bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one;
  P_Q_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_grd_r_act_is_two_grd_bimod
    :> @IsTwoGrdBimod A P Q bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg grd_l_act grd_r_act;
  P_Q_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_grd_r_act_grd_mul_is_grd_bilin_op
    :> @IsGrdBilinOp A P Q bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg grd_l_act grd_r_act grd_mul;
}.
