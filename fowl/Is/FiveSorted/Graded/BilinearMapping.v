From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction
  ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.Graded.LeftModule TwoSorted.Graded.RightModule
  ThreeSorted.Graded.Bimodule
  ThreeSorted.Graded.Biadditive FiveSorted.Graded.Bihomogeneous.

(** Graded bilinear mapping
    from a graded left module and a graded right module into a graded bimodule,
    where each module is defined over a graded noncommutative ring.
    The grading is carried by [A], the rings by [P] and [Q],
    the left module by [R], the right module by [S] and the bimodule by [T].
    See [Is.FiveSorted.BilinearMapping]. *)

Class IsGrdBilinMap {A : Type} (P Q R S T : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (Q_has_grd_mul : HasGrdMul Q) (Q_has_grd_one : HasGrdOne Q)
  (R_has_add : forall i : A, HasAdd (R i))
  (R_has_zero : forall i : A, HasZero (R i))
  (R_has_neg : forall i : A, HasNeg (R i))
  (S_has_add : forall i : A, HasAdd (S i))
  (S_has_zero : forall i : A, HasZero (S i))
  (S_has_neg : forall i : A, HasNeg (S i))
  (T_has_add : forall i : A, HasAdd (T i))
  (T_has_zero : forall i : A, HasZero (T i))
  (T_has_neg : forall i : A, HasNeg (T i))
  (P_R_has_grd_l_act : HasGrdLAct P R) (Q_S_has_grd_r_act : HasGrdRAct Q S)
  (P_T_has_grd_l_act : HasGrdLAct P T) (Q_T_has_grd_r_act : HasGrdRAct Q T)
  (R_S_T_has_grd_bin_fn : HasGrdBinFn R S T) : Prop := {
  P_R_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_is_grd_l_mod :>
    IsGrdLMod P R P_has_add P_has_zero P_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_l_act;
  Q_S_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_r_act_is_grd_r_mod :>
    IsGrdRMod Q S Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    S_has_add S_has_zero S_has_neg grd_r_act;
  P_Q_T_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_grd_r_act_is_three_grd_bimod
    :> IsThreeGrdBimod P Q T
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    T_has_add T_has_zero T_has_neg grd_l_act grd_r_act;
  R_S_T_add_add_add_grd_bin_fn_is_grd_biaddve :>
    IsGrdBiaddve R S T R_has_add S_has_add T_has_add grd_bin_fn;
  P_Q_R_S_T_grd_l_act_grd_r_act_grd_l_act_grd_r_act_grd_bin_fn_is_grd_bihomogen
    :> IsGrdBihomogen P Q R S T
    grd_l_act grd_r_act grd_l_act grd_r_act grd_bin_fn;
}.
