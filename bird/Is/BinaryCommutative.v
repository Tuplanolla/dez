From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.Is Require Export
  LeftBinaryCommutative RightBinaryCommutative ExternallyBinaryCommutative.

(** TODO This is nonsense and should be called some sort of distributivity. *)

Class IsBinComm {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop := {
  bin_op_un_op_is_l_bin_comm :> IsLBinComm bin_op un_op;
  bin_op_un_op_is_r_bin_comm :> IsRBinComm bin_op un_op;
}.

Section Context.

Context {A : Type} `{is_bin_comm : IsBinComm A}.

Global Instance bin_op_un_op_is_ext_bin_comm : IsExtBinComm bin_op un_op.
Proof.
  constructor.
  - destruct is_bin_comm; typeclasses eauto.
  - destruct is_bin_comm; typeclasses eauto. Qed.

End Context.
