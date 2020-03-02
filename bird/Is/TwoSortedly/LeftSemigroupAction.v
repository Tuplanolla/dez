From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation LeftAction.
From Maniunfold.Is Require Export
  Semigroup LeftCompatible.

Class IsLSgrpAct {A B : Type} {A_has_eq_rel : HasEqRel A}
  {B_has_eq_rel : HasEqRel B} (has_bin_op : HasBinOp A)
  (has_l_act : HasLAct A B) : Prop := {
  bin_op_is_sgrp :> IsSgrp bin_op;
  bin_op_l_act_is_l_compat :> IsLCompat bin_op l_act;
}.
