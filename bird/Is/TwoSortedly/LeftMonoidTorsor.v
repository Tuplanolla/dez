From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation NullaryOperation
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Monoid LeftGroupAction LeftUnique.

(** TODO Does this weakening from groups to monoids even make sense? *)

Class IsLMonTor {A B : Type}
  (has_bin_op : HasBinOp A) (has_un : HasNullOp A)
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop := {
  bin_op_null_op_l_act_is_l_mon_act :> IsLMonAct bin_op null_op l_act;
  l_act_l_tor_left_uniq :> IsLUniq l_act l_tor;
}.
