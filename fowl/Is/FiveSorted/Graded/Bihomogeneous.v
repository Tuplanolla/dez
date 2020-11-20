(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction
  ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  FourSorted.Graded.LeftBihomogeneous FourSorted.Graded.RightBihomogeneous.

Class IsGrdBihomogen (A : Type) (P Q R S T : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!@HasGrdLAct A P R bin_op) `(!@HasGrdRAct A Q S bin_op)
  `(!@HasGrdLAct A P T bin_op) `(!@HasGrdRAct A Q T bin_op)
  `(!@HasGrdBinFn A R S T bin_op) : Prop := {
  P_R_S_T_grd_l_act_grd_l_act_grd_bin_fn_is_grd_l_bihomogen :>
    @IsGrdLBihomogen A P R S T bin_op grd_l_act grd_l_act grd_bin_fn;
  Q_R_S_T_grd_r_act_grd_r_act_grd_bin_fn_is_grd_r_bihomogen :>
    @IsGrdRBihomogen A Q R S T bin_op grd_r_act grd_r_act grd_bin_fn;
}.
