From Coq Require Import
  PArith.PArith.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid.

Module Additive.

Global Instance positive_has_bin_op : HasBinOp positive := Pos.add.

Global Instance positive_bin_op_is_mag : IsMag (bin_op (A := positive)).
Proof. Defined.

Global Instance positive_bin_op_is_assoc : IsAssoc (bin_op (A := positive)).
Proof. intros x y z. apply Pos.add_assoc. Defined.

Global Instance positive_bin_op_is_sgrp : IsSgrp (bin_op (A := positive)).
Proof. split; typeclasses eauto. Defined.

Global Instance positive_bin_op_is_comm : IsComm (bin_op (A := positive)).
Proof. intros x y. apply Pos.add_comm. Defined.

Global Instance positive_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := positive)).
Proof. split; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance positive_bin_op_has_bin_op : HasBinOp positive := Pos.mul.
Global Instance positive_has_null_op : HasNullOp positive := xH.

Global Instance positive_bin_op_is_mag : IsMag (bin_op (A := positive)).
Proof. Defined.

Global Instance positive_bin_op_is_assoc : IsAssoc (bin_op (A := positive)).
Proof. intros x y z. apply Pos.mul_assoc. Defined.

Global Instance positive_bin_op_is_sgrp : IsSgrp (bin_op (A := positive)).
Proof. split; typeclasses eauto. Defined.

Global Instance positive_bin_op_is_comm : IsComm (bin_op (A := positive)).
Proof. intros x y. apply Pos.mul_comm. Defined.

Global Instance positive_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := positive)).
Proof. split; typeclasses eauto. Defined.

Global Instance positive_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := positive)) null_op.
Proof. intros x. apply Pos.mul_1_l. Defined.

Global Instance positive_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := positive)) null_op.
Proof. intros x. apply Pos.mul_1_r. Defined.

Global Instance positive_bin_op_null_op_is_unl : IsUnl (bin_op (A := positive)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance positive_bin_op_null_op_is_mon : IsMon (bin_op (A := positive)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance positive_bin_op_null_op_is_comm_mon : IsCommMon (bin_op (A := positive)) null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.
