From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid OneSorted.CommutativeSemiring
  OneSorted.CommutativeRing.

Ltac eautodestruct :=
  repeat match goal with
  | x : unit |- _ => destruct x
  end; eauto.

Module Additive.

Global Instance unit_has_bin_op : HasBinOp unit := fun x y : unit => tt.
Global Instance unit_has_null_op : HasNullOp unit := tt.
Global Instance unit_has_un_op : HasUnOp unit := fun x : unit => tt.

Global Instance unit_bin_op_is_mag : IsMag unit bin_op.
Proof. Defined.

Global Instance unit_bin_op_is_assoc : IsAssoc unit bin_op.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_bin_op_is_sgrp : IsSgrp unit bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_is_comm : IsComm unit bin_op.
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_bin_op_is_comm_sgrp : IsCommSgrp unit bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_l_unl : IsLUnl unit bin_op null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_r_unl : IsRUnl unit bin_op null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl : IsUnl unit bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_mon : IsMon unit bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_comm_mon :
  IsCommMon unit bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_l_inv :
  IsLInv unit bin_op null_op un_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_un_op_is_r_inv :
  IsRInv unit bin_op null_op un_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_un_op_is_inv :
  IsInv unit bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_grp :
  IsGrp unit bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_un_op_is_ab_grp :
  IsAbGrp unit bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance unit_bin_op_has_bin_op : HasBinOp unit := fun x y : unit => tt.
Global Instance unit_has_null_op : HasNullOp unit := tt.

Global Instance unit_bin_op_is_mag : IsMag unit bin_op.
Proof. Defined.

Global Instance unit_bin_op_is_assoc : IsAssoc unit bin_op.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_bin_op_is_sgrp : IsSgrp unit bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_is_comm : IsComm unit bin_op.
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_bin_op_is_comm_sgrp : IsCommSgrp unit bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_l_unl : IsLUnl unit bin_op null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_r_unl : IsRUnl unit bin_op null_op.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_bin_op_null_op_is_unl : IsUnl unit bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_mon : IsMon unit bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_bin_op_null_op_is_comm_mon :
  IsCommMon unit bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.

Global Instance unit_has_add : HasAdd unit := bin_op.
Global Instance unit_has_zero : HasZero unit := null_op.
Global Instance unit_has_neg : HasNeg unit := un_op.
Global Instance unit_has_mul : HasMul unit := bin_op.
Global Instance unit_has_one : HasOne unit := null_op.

Global Instance unit_add_is_comm : IsComm unit add.
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_add_mul_is_l_distr : IsLDistr unit add mul.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_add_mul_is_r_distr : IsRDistr unit add mul.
Proof. intros x y z. eautodestruct. Defined.

Global Instance unit_add_mul_is_distr : IsDistr unit add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_zero_mul_is_l_absorb : IsLAbsorb unit zero mul.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_zero_mul_is_r_absorb : IsRAbsorb unit zero mul.
Proof. intros x. eautodestruct. Defined.

Global Instance unit_zero_mul_is_absorb : IsAbsorb unit zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_add_zero_mul_one_is_sring : IsSring unit add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_add_zero_mul_one_is_comm_sring :
  IsCommSring unit add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_add_zero_neg_mul_one_is_ring :
  IsRing unit add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance unit_mul_is_comm : IsComm unit mul.
Proof. intros x y. eautodestruct. Defined.

Global Instance unit_add_zero_neg_mul_one_is_comm_ring :
  IsCommRing unit add zero neg mul one.
Proof. split; typeclasses eauto. Defined.
