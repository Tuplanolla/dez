(* bad *)
From DEZ.Has Require Export
  BinaryOperation Action.
From DEZ.Is Require Export
  Semigroup TwoSortedLeftCompatible.

Class IsLSemigrpAct (A B : Type)
  `(HasBinOp A) `(HasActL A B) : Prop := {
  A_bin_op_is_semigrp :> IsSemigrp (bin_op (A := A));
  (* A_B_bin_op_act_l_is_l_semigrp_act :> IsLMagAct bin_op act_l; *)
  A_B_bin_op_act_l_is_l_compat :> IsLCompat bin_op act_l;
}.
