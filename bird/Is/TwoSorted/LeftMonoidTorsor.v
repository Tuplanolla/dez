From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Monoid LeftGroupAction LeftUnique.

(** TODO Does this weakening from groups to monoids even make sense? *)

Class IsLMonTor {A B : Type}
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A)
  (A_B_has_l_act : HasLAct A B) (A_B_has_l_tor : HasLTor A B) : Prop := {
  bin_op_null_op_l_act_is_l_mon_act :> IsLMonAct bin_op null_op l_act;
  l_act_l_tor_left_uniq :> IsLNullUniq l_act l_tor;
}.
