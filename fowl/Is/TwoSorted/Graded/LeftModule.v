From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  TwoSorted.Graded.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Graded.Ring OneSorted.AbelianGroup
  TwoSorted.Graded.LeftRightDistributive TwoSorted.Graded.LeftCompatible
  TwoSorted.Graded.LeftUnital TwoSorted.Graded.LeftLeftDistributive.

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
  P_add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing P bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one;
  Q_add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  P_Q_add_add_grd_l_act_is_grd_two_r_distr :>
    IsTwoGrdLRDistr P Q bin_op null_op P_has_add Q_has_add grd_l_act;
  P_Q_grd_mul_grd_l_act_is_grd_l_compat :>
    IsGrdLCompat P Q bin_op null_op grd_mul grd_l_act;
  P_Q_zero_grd_l_act_is_grd_two_l_unl :>
    IsTwoGrdLUnl P Q bin_op null_op grd_l_act grd_one;
  P_Q_add_grd_l_act_is_grd_two_l_distr :>
    IsTwoGrdLLDistr P Q bin_op null_op Q_has_add grd_l_act;
}.
