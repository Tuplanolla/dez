(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Semigroup TwoSorted.LeftMagmaAction TwoSorted.LeftCompatible.

Class IsLSgrpAct (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_B_has_l_act : HasLAct A B) : Prop := {
  A_bin_op_is_sgrp :> IsSgrp (A := A) bin_op;
  A_B_bin_op_l_act_is_l_sgrp_act :> IsLMagAct A B bin_op l_act;
  A_B_bin_op_l_act_is_l_compat :> IsLCompat A B bin_op l_act;
}.
