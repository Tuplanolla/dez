From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Monoid LeftGroupAction LeftUnique.

(** TODO Does this weakening from groups to monoids even make sense? *)

Class IsLMonTor {A B : Type}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop := {
  bin_op_un_l_act_is_l_mon_act :> IsLMonAct bin_op un l_act;
  l_act_l_tor_left_uniq :> IsLUniq l_act l_tor;
}.
