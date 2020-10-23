(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Semigroup TwoSorted.LeftMagmaAction TwoSorted.LeftCompatible.

Class IsLSgrpAct (A B : Type)
  `(HasBinOp A) `(HasLAct A B) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp A bin_op;
  A_B_bin_op_l_act_is_l_sgrp_act :> IsLMagAct A B bin_op l_act;
  A_B_bin_op_l_act_is_l_compat :> IsLCompat A B bin_op l_act;
}.
