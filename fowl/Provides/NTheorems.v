From Coq Require Import
  NArith.NArith.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid OneSorted.CommutativeSemiring.

Module Additive.

Global Instance N_has_bin_op : HasBinOp N := N.add.
Global Instance N_has_null_op : HasNullOp N := N.zero.

Global Instance N_bin_op_is_mag : IsMag (bin_op (A := N)).
Proof. Defined.

Global Instance N_bin_op_is_assoc : IsAssoc (bin_op (A := N)).
Proof. intros x y z. apply N.add_assoc. Defined.

Global Instance N_bin_op_is_sgrp : IsSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_is_comm : IsComm (bin_op (A := N)).
Proof. intros x y. apply N.add_comm. Defined.

Global Instance N_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.add_0_l. Defined.

Global Instance N_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.add_0_r. Defined.

Global Instance N_bin_op_null_op_is_unl : IsUnl (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_mon : IsMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_comm_mon : IsCommMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance N_bin_op_has_bin_op : HasBinOp N := N.mul.
Global Instance N_has_null_op : HasNullOp N := N.one.

Global Instance N_bin_op_is_mag : IsMag (bin_op (A := N)).
Proof. Defined.

Global Instance N_bin_op_is_assoc : IsAssoc (bin_op (A := N)).
Proof. intros x y z. apply N.mul_assoc. Defined.

Global Instance N_bin_op_is_sgrp : IsSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_is_comm : IsComm (bin_op (A := N)).
Proof. intros x y. apply N.mul_comm. Defined.

Global Instance N_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.mul_1_l. Defined.

Global Instance N_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.mul_1_r. Defined.

Global Instance N_bin_op_null_op_is_unl : IsUnl (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_mon : IsMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_comm_mon : IsCommMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.

Global Instance N_has_add : HasAdd N := N.add.
Global Instance N_has_zero : HasZero N := N.zero.
Global Instance N_has_mul : HasMul N := N.mul.
Global Instance N_has_one : HasOne N := N.one.

Global Instance N_add_is_comm : IsComm add.
Proof. intros x y. apply N.add_comm. Defined.

Global Instance N_add_mul_is_l_distr : IsLDistr add mul.
Proof. intros x y z. apply N.mul_add_distr_l. Defined.

Global Instance N_add_mul_is_r_distr : IsRDistr add mul.
Proof. intros x y z. apply N.mul_add_distr_r. Defined.

Global Instance N_add_mul_is_distr : IsDistr add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance N_zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. intros x. apply N.mul_0_l. Defined.

Global Instance N_zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. intros x. apply N.mul_0_r. Defined.

Global Instance N_zero_mul_is_absorb : IsAbsorb zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance N_add_zero_mul_one_is_sring : IsSring add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance N_mul_is_comm : IsComm mul.
Proof. intros x y. apply N.mul_comm. Defined.

Global Instance N_add_zero_mul_one_is_comm_sring :
  IsCommSring add zero mul one.
Proof. split; typeclasses eauto. Defined.
