(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  ThreeSorted.LeftBiadditive ThreeSorted.RightBiadditive.

Class IsBiaddve (A B C : Type)
  `(HasAdd A) `(HasAdd B) `(HasAdd C)
  `(HasBinFn A B C) : Prop := {
  A_B_C_add_add_bin_fn_is_l_biaddve :> IsLBiaddve A B C add add bin_fn;
  A_B_C_add_add_bin_fn_is_r_biaddve :> IsRBiaddve A B C add add bin_fn;
}.
