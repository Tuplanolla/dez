From Maniunfold.Is Require Export
  OneSortedAbelianGroup Semigroup
  Monoid OneSortedSemiring
  OneSortedRing OneSortedCommutativeSemigroup OneSortedCommutativeMonoid
  OneSortedCommutativeSemiring OneSortedCommutativeRing.

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

Global Instance unit_bin_op_is_semigrp : IsSemigrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_is_comm : IsComm (bin_op (A := unit)).
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_bin_op_is_comm_semigrp : IsCommSemigrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_unl_l : IsUnlBinOpL null_op (bin_op (A := unit)).
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl_r : IsUnlBinOpR null_op (bin_op (A := unit)).
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl : IsUnlBinOpLR null_op (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_mon : IsMon null_op (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_comm_mon :
  IsCommMon (bin_op (A := unit)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_inv_l_hom :
  IsInvL null_op un_op (bin_op (A := unit)).
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_un_op_is_inv_r_hom :
  IsInvR null_op un_op (bin_op (A := unit)).
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_un_op_is_inv_hom :
  IsInvLR null_op un_op (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_grp :
  IsGrp null_op un_op (bin_op (A := unit)).
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

Global Instance unit_bin_op_is_semigrp : IsSemigrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_is_comm : IsComm (bin_op (A := unit)).
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_bin_op_is_comm_semigrp : IsCommSemigrp (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_unl_l : IsUnlBinOpL null_op (bin_op (A := unit)).
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl_r : IsUnlBinOpR null_op (bin_op (A := unit)).
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl : IsUnlBinOpLR null_op (bin_op (A := unit)).
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_mon : IsMon null_op (bin_op (A := unit)).
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

Global Instance unit_add_mul_is_distr_l : IsDistrL mul add.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_add_mul_is_distr_r : IsDistrR mul add.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_add_mul_is_distr : IsDistrLR mul add.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_zero_mul_is_absorb_elem_l : IsAbsorbElemL zero mul.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_zero_mul_is_absorb_elem_r : IsAbsorbElemR zero mul.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_zero_mul_is_absorb_elem_l_r : IsAbsorbElemLR zero mul.
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
