From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid OneSorted.CommutativeSemiring
  OneSorted.CommutativeRing
  OneSorted.Equivalence TwoSorted.Isomorphism.

Module Additive.

Global Instance Z_has_bin_op : HasBinOp Z := Z.add.
Global Instance Z_has_null_op : HasNullOp Z := Z.zero.
Global Instance Z_has_un_op : HasUnOp Z := Z.opp.

Global Instance Z_bin_op_is_mag : IsMag Z bin_op.
Proof. Defined.

Global Instance Z_bin_op_is_assoc : IsAssoc Z bin_op.
Proof. intros x y z. apply Z.add_assoc. Defined.

Global Instance Z_bin_op_is_sgrp : IsSgrp Z bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_is_comm : IsComm Z bin_op.
Proof. intros x y. apply Z.add_comm. Defined.

Global Instance Z_bin_op_is_comm_sgrp : IsCommSgrp Z bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_l_unl : IsLUnl Z bin_op null_op.
Proof. intros x. apply Z.add_0_l. Defined.

Global Instance Z_bin_op_null_op_is_r_unl : IsRUnl Z bin_op null_op.
Proof. intros x. apply Z.add_0_r. Defined.

Global Instance Z_bin_op_null_op_is_unl : IsUnl Z bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_mon : IsMon Z bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_comm_mon : IsCommMon Z bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_un_op_is_l_inv :
  IsLInv Z bin_op null_op un_op.
Proof. intros x. apply Z.add_opp_diag_l. Defined.

Global Instance Z_bin_op_null_op_un_op_is_r_inv :
  IsRInv Z bin_op null_op un_op.
Proof. intros x. apply Z.add_opp_diag_r. Defined.

Global Instance Z_bin_op_null_op_un_op_is_inv : IsInv Z bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_un_op_is_grp : IsGrp Z bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_un_op_is_ab_grp :
  IsAbGrp Z bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance Z_bin_op_has_bin_op : HasBinOp Z := Z.mul.
Global Instance Z_has_null_op : HasNullOp Z := Z.one.

Global Instance Z_bin_op_is_mag : IsMag Z bin_op.
Proof. Defined.

Global Instance Z_bin_op_is_assoc : IsAssoc Z bin_op.
Proof. intros x y z. apply Z.mul_assoc. Defined.

Global Instance Z_bin_op_is_sgrp : IsSgrp Z bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_is_comm : IsComm Z bin_op.
Proof. intros x y. apply Z.mul_comm. Defined.

Global Instance Z_bin_op_is_comm_sgrp : IsCommSgrp Z bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_l_unl : IsLUnl Z bin_op null_op.
Proof. intros x. apply Z.mul_1_l. Defined.

Global Instance Z_bin_op_null_op_is_r_unl : IsRUnl Z bin_op null_op.
Proof. intros x. apply Z.mul_1_r. Defined.

Global Instance Z_bin_op_null_op_is_unl : IsUnl Z bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_mon : IsMon Z bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_comm_mon : IsCommMon Z bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.

Global Instance Z_has_add : HasAdd Z := Z.add.
Global Instance Z_has_zero : HasZero Z := Z.zero.
Global Instance Z_has_neg : HasNeg Z := Z.opp.
Global Instance Z_has_mul : HasMul Z := Z.mul.
Global Instance Z_has_one : HasOne Z := Z.one.

Global Instance Z_add_is_comm : IsComm Z add.
Proof. intros x y. apply Z.add_comm. Defined.

Global Instance Z_add_mul_is_l_distr : IsLDistr Z add mul.
Proof. intros x y z. apply Z.mul_add_distr_l. Defined.

Global Instance Z_add_mul_is_r_distr : IsRDistr Z add mul.
Proof. intros x y z. apply Z.mul_add_distr_r. Defined.

Global Instance Z_add_mul_is_distr : IsDistr Z add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_zero_mul_is_l_absorb : IsLAbsorb Z zero mul.
Proof. intros x. apply Z.mul_0_l. Defined.

Global Instance Z_zero_mul_is_r_absorb : IsRAbsorb Z zero mul.
Proof. intros x. apply Z.mul_0_r. Defined.

Global Instance Z_zero_mul_is_absorb : IsAbsorb Z zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_add_zero_mul_one_is_sring : IsSring Z add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_add_zero_mul_one_is_comm_sring :
  IsCommSring Z add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_add_zero_neg_mul_one_is_ring : IsRing Z add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_mul_is_comm : IsComm Z mul.
Proof. intros x y. apply Z.mul_comm. Defined.

Global Instance Z_add_zero_neg_mul_one_is_comm_ring :
  IsCommRing Z add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

(** TODO Organize the rest. *)

Global Instance Z_has_eq_rel : HasEqRel Z := Z.eq.

Global Instance Z_eq_is_refl : IsRefl Z eq.
Proof. intros x. reflexivity. Defined.

Global Instance Z_eq_is_sym : IsSym Z eq.
Proof. intros x y p. symmetry; auto. Defined.

Global Instance Z_eq_is_trans : IsTrans Z eq.
Proof. intros x y z p q. transitivity y; auto. Defined.

Global Instance Z_eq_is_part_eq : IsPartEq Z eq.
Proof. split; typeclasses eauto. Defined.

Global Instance Z_eq_is_eq : IsEq Z eq.
Proof. split; typeclasses eauto. Defined.

(** This is the sign--parity isomorphism. *)

Definition Z_to_double_N (n : Z) : N :=
  match n with
  | Z0 => N0
  | Zpos p => Npos (xO p)
  | Zneg p => Npos (Pos.pred_double p)
  end.

Definition Z_of_double_N (n : N) : Z :=
  match n with
  | N0 => Z0
  | Npos p => match p with
    | xI q => Zneg (Pos.succ q)
    | xO q => Zpos q
    | xH => Zneg xH
    end
  end.

Global Instance Z_N_has_iso : HasIso Z N := (Z_to_double_N, Z_of_double_N).

Global Instance Z_N_is_iso : IsIso Z N iso.
Proof.
  split.
  - intros x. destruct x as [| p | p].
    + reflexivity.
    + reflexivity.
    + destruct p as [q | q |].
      * reflexivity.
      * cbn. rewrite (Pos.succ_pred_double q). reflexivity.
      * reflexivity.
  - intros x. destruct x as [| p].
    + reflexivity.
    + destruct p as [q | q |].
      * cbn. rewrite (Pos.pred_double_succ q). reflexivity.
      * reflexivity.
      * reflexivity. Defined.
