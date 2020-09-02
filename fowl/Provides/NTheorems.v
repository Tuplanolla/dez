From Coq Require Import
  NArith.NArith.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid OneSorted.CommutativeSemiring.

Module Additive.

Global Instance N_has_bin_op : HasBinOp N := N.add.
Global Instance N_has_null_op : HasNullOp N := N.zero.

Global Instance N_bin_op_is_mag : IsMag N bin_op.
Proof. Defined.

Global Instance N_bin_op_is_assoc : IsAssoc N bin_op.
Proof. intros x y z. apply N.add_assoc. Defined.

Global Instance N_bin_op_is_sgrp : IsSgrp N bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_is_comm : IsComm N bin_op.
Proof. intros x y. apply N.add_comm. Defined.

Global Instance N_bin_op_is_comm_sgrp : IsCommSgrp N bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_l_unl : IsLUnl N bin_op null_op.
Proof. intros x. apply N.add_0_l. Defined.

Global Instance N_bin_op_null_op_is_r_unl : IsRUnl N bin_op null_op.
Proof. intros x. apply N.add_0_r. Defined.

Global Instance N_bin_op_null_op_is_unl : IsUnl N bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_mon : IsMon N bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_comm_mon : IsCommMon N bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance N_bin_op_has_bin_op : HasBinOp N := N.mul.
Global Instance N_has_null_op : HasNullOp N := N.one.

Global Instance N_bin_op_is_mag : IsMag N bin_op.
Proof. Defined.

Global Instance N_bin_op_is_assoc : IsAssoc N bin_op.
Proof. intros x y z. apply N.mul_assoc. Defined.

Global Instance N_bin_op_is_sgrp : IsSgrp N bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_is_comm : IsComm N bin_op.
Proof. intros x y. apply N.mul_comm. Defined.

Global Instance N_bin_op_is_comm_sgrp : IsCommSgrp N bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_l_unl : IsLUnl N bin_op null_op.
Proof. intros x. apply N.mul_1_l. Defined.

Global Instance N_bin_op_null_op_is_r_unl : IsRUnl N bin_op null_op.
Proof. intros x. apply N.mul_1_r. Defined.

Global Instance N_bin_op_null_op_is_unl : IsUnl N bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_mon : IsMon N bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_comm_mon : IsCommMon N bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.

Global Instance N_has_add : HasAdd N := N.add.
Global Instance N_has_zero : HasZero N := N.zero.
Global Instance N_has_mul : HasMul N := N.mul.
Global Instance N_has_one : HasOne N := N.one.

Global Instance N_add_is_comm : IsComm N add.
Proof. intros x y. apply N.add_comm. Defined.

Global Instance N_add_mul_is_l_distr : IsLDistr N add mul.
Proof. intros x y z. apply N.mul_add_distr_l. Defined.

Global Instance N_add_mul_is_r_distr : IsRDistr N add mul.
Proof. intros x y z. apply N.mul_add_distr_r. Defined.

Global Instance N_add_mul_is_distr : IsDistr N add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance N_zero_mul_is_l_absorb : IsLAbsorb N zero mul.
Proof. intros x. apply N.mul_0_l. Defined.

Global Instance N_zero_mul_is_r_absorb : IsRAbsorb N zero mul.
Proof. intros x. apply N.mul_0_r. Defined.

Global Instance N_zero_mul_is_absorb : IsAbsorb N zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance N_add_zero_mul_one_is_sring : IsSring N add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance N_mul_is_comm : IsComm N mul.
Proof. intros x y. apply N.mul_comm. Defined.

Global Instance N_add_zero_mul_one_is_comm_sring :
  IsCommSring N add zero mul one.
Proof. split; typeclasses eauto. Defined.
