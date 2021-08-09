(* bad *)
From DEZ.Has Require Export
  Action ThreeSortedBinaryFunction.
From DEZ.Is Require Export
  FourSortedLeftBihomogeneous FourSortedRightBihomogeneous.

Class IsBihomogen (A B C D E : Type)
  `(HasActL A C) `(HasActR B D)
  `(HasActL A E) `(HasActR B E)
  `(HasBinFn C D E) : Prop := {
  A_C_D_E_act_l_act_l_bin_fn_is_l_bihomogen :>
    @IsLBihomogen A C D E act_l act_l bin_fn;
  B_C_D_E_act_r_act_r_bin_fn_is_r_bihomogen :>
    @IsRBihomogen B C D E act_r act_r bin_fn;
}.
