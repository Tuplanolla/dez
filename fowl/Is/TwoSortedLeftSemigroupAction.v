(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation Action.
From Maniunfold.Is Require Export
  OneSortedSemigroup TwoSortedLeftMagmaAction TwoSortedLeftCompatible.

Class IsLSgrpAct (A B : Type)
  `(HasBinOp A) `(HasActL A B) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp (bin_op (A := A));
  A_B_bin_op_act_l_is_l_sgrp_act :> IsLMagAct bin_op act_l;
  A_B_bin_op_act_l_is_l_compat :> IsLCompat bin_op act_l;
}.
