(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  FourSorted.LeftBihomogeneous FourSorted.RightBihomogeneous.

Class IsBihomogen (A B C D E : Type)
  `(HasLAct A C) `(HasRAct B D)
  `(HasLAct A E) `(HasRAct B E)
  `(HasBinFn C D E) : Prop := {
  A_C_D_E_l_act_l_act_bin_fn_is_l_bihomogen :>
    @IsLBihomogen A C D E l_act l_act bin_fn;
  B_C_D_E_r_act_r_act_bin_fn_is_r_bihomogen :>
    @IsRBihomogen B C D E r_act r_act bin_fn;
}.
