(* bad *)
From DEZ.Has Require Export
  BinaryOperation NullaryOperation
  GradedAction GradedAction
  ThreeSortedGradedBinaryFunction.
From DEZ.Is Require Export
  FourSortedGradedLeftBihomogeneous FourSortedGradedRightBihomogeneous.

Class IsGrdBihomogen (A : Type) (P Q R S T : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(!@HasGrdActL A P R bin_op) `(!@HasGrdActR A Q S bin_op)
  `(!@HasGrdActL A P T bin_op) `(!@HasGrdActR A Q T bin_op)
  `(!@HasGrdBinFn A R S T bin_op) : Prop := {
  P_R_S_T_grd_act_l_grd_act_l_grd_bin_fn_is_grd_l_bihomogen :>
    @IsGrdLBihomogen A P R S T bin_op grd_act_l grd_act_l grd_bin_fn;
  Q_R_S_T_grd_act_r_grd_act_r_grd_bin_fn_is_grd_r_bihomogen :>
    @IsGrdRBihomogen A Q R S T bin_op grd_act_r grd_act_r grd_bin_fn;
}.
