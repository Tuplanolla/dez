(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  ThreeSorted.LeftBiadditive ThreeSorted.RightBiadditive.

Class IsBiaddve (A B C : Type)
  `(HasAdd A) `(HasAdd B) `(HasAdd C)
  `(HasBinFn A B C) : Prop := {
  A_B_C_add_add_bin_fn_is_l_biaddve :>
    IsLBiaddve (add (A := A)) (add (A := C)) bin_fn;
  A_B_C_add_add_bin_fn_is_r_biaddve :>
    IsRBiaddve (add (A := B)) (add (A := C)) bin_fn;
}.
