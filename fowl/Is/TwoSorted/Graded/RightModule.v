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

Class IsGrdRMod {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  P_add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing P P_has_add P_has_zero P_has_neg grd_mul grd_one;
  Q_add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (Q i) (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  P_Q_add_add_grd_r_act_is_grd_two_r_distr :>
    IsTwoGrdRLDistr P Q P_has_add Q_has_add grd_r_act;
  P_Q_grd_mul_grd_r_act_is_grd_r_compat :> IsGrdRCompat P Q grd_mul grd_r_act;
  P_Q_zero_grd_r_act_is_grd_two_r_unl :> IsTwoGrdRUnl P Q grd_r_act grd_one;
  P_Q_add_grd_r_act_is_grd_two_r_distr :>
    IsTwoGrdRRDistr P Q Q_has_add grd_r_act;
}.
