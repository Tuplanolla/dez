From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  TwoSorted.Graded.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Graded.Ring OneSorted.AbelianGroup
  TwoSorted.Graded.RightLeftDistributive TwoSorted.Graded.RightCompatible
  TwoSorted.Graded.RightUnital TwoSorted.Graded.RightRightDistributive.

(** Graded module over a noncommutative ring; right chirality.
    See [Is.TwoSorted.Graded.LeftModule]. *)

Class IsGrdRMod (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!@HasGrdMul A P bin_op) `(!@HasGrdOne A P null_op)
  `(Q_has_add : forall i : A, HasAdd (Q i))
  `(Q_has_zero : forall i : A, HasZero (Q i))
  `(Q_has_neg : forall i : A, HasNeg (Q i))
  `(!@HasGrdRAct A P Q bin_op) : Prop := {
  add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing bin_op null_op P_has_add P_has_zero P_has_neg grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  add_add_grd_r_act_is_grd_two_r_distr :>
    @IsTwoGrdRLDistr A P Q bin_op null_op P_has_add Q_has_add grd_r_act;
  grd_mul_grd_r_act_is_grd_r_compat :>
    @IsGrdRCompat A P Q bin_op null_op grd_mul grd_r_act;
  zero_grd_r_act_is_grd_two_r_unl :>
    @IsTwoGrdRUnl A P Q bin_op null_op grd_r_act grd_one;
  add_grd_r_act_is_grd_two_r_distr :>
    @IsTwoGrdRRDistr A P Q bin_op null_op Q_has_add grd_r_act;
}.
