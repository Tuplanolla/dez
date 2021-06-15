From Maniunfold.Is Require Export
  OneSortedAbelianGroup OneSortedCommutativeSemigroup
  OneSortedCommutativeMonoid OneSortedCommutativeSemiring
  OneSortedCommutativeRing.

Ltac eautodestruct :=
  repeat match goal with
  | x : unit |- _ => destruct x
  end; eauto.

Module Additive.

Global Instance unit_has_bin_op : HasBinOp unit := fun x y : unit => tt.
Global Instance unit_has_null_op : HasNullOp unit := tt.
Global Instance unit_has_un_op : HasUnOp unit := fun x : unit => tt.

Global Instance unit_bin_op_is_mag : IsMag (bin_op (A := unit)).
Proof. Defined.

Global Instance unit_bin_op_is_assoc : IsAssoc (bin_op (A := unit)).
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_bin_op_is_sgrp : IsSgrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_is_comm : IsComm (bin_op (A := unit)).
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := unit)) null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := unit)) null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl : IsUnl (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_mon : IsMon (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_comm_mon :
  IsCommMon (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_l_inv_hom :
  IsLInv (bin_op (A := unit)) null_op un_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_un_op_is_r_inv_hom :
  IsRInv (bin_op (A := unit)) null_op un_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_un_op_is_inv_hom :
  IsInv (bin_op (A := unit)) null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_grp :
  IsGrp (bin_op (A := unit)) null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_ab_grp :
  IsAbGrp (bin_op (A := unit)) null_op un_op.
Proof. split; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance unit_bin_op_has_bin_op : HasBinOp unit := fun x y : unit => tt.
Global Instance unit_has_null_op : HasNullOp unit := tt.

Global Instance unit_bin_op_is_mag : IsMag (bin_op (A := unit)).
Proof. Defined.

Global Instance unit_bin_op_is_assoc : IsAssoc (bin_op (A := unit)).
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_bin_op_is_sgrp : IsSgrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_is_comm : IsComm (bin_op (A := unit)).
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := unit)) null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := unit)) null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl : IsUnl (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_mon : IsMon (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_comm_mon :
  IsCommMon (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.

Global Instance unit_has_add : HasAdd unit := bin_op.
Global Instance unit_has_zero : HasZero unit := null_op.
Global Instance unit_has_neg : HasNeg unit := un_op.
Global Instance unit_has_mul : HasMul unit := bin_op.
Global Instance unit_has_one : HasOne unit := null_op.

Global Instance unit_add_is_comm : IsComm add.
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_add_mul_is_l_distr : IsLDistr add mul.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_add_mul_is_r_distr : IsRDistr add mul.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_add_mul_is_distr : IsDistr add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_zero_mul_is_absorb : IsAbsorb zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_add_zero_mul_one_is_semiring : IsSemiring add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_add_zero_mul_one_is_comm_semiring :
  IsCommSemiring add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_add_zero_neg_mul_one_is_ring :
  IsRing add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_mul_is_comm : IsComm mul.
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_add_zero_neg_mul_one_is_comm_ring :
  IsCommRing add zero neg mul one.
Proof. split; typeclasses eauto. Defined.
