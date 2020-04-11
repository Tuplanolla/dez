(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation UnaryOperation LeftAction.
From Maniunfold.Is Require Export
  Group LeftMonoidAction.

Class IsLGrpAct (A B : Type)
  (A_has_bin_op : HasBinOp A) (A_has_null_op : HasNullOp A)
  (A_has_un_op : HasUnOp A) (A_B_has_l_act : HasLAct A B) : Prop := {
  A_bin_op_null_op_un_op_is_grp :> IsGrp A bin_op null_op un_op;
  A_B_bin_op_null_op_l_act_is_l_mon_act :> IsLMonAct A B bin_op null_op l_act;
  (** TODO This property. *)
  two_l_inv : forall x : A, l_act (un_op x) x = null_op;
}.
