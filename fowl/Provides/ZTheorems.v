From Coq Require Import
  ZArith.ZArith.
From DEZ.Is Require Export
  AbelianGroup Semigroup
  Monoid Semiring Ring
  Equivalence PartialEquivalence Isomorphism.

Module Additive.

Global Instance Z_has_bin_op : HasBinOp Z := Z.add.
Global Instance Z_has_null_op : HasNullOp Z := Z.zero.
Global Instance Z_has_un_op : HasUnOp Z := Z.opp.

Global Instance Z_bin_op_is_mag : IsMag eq (bin_op (A := Z)).
Proof. hnf. typeclasses eauto. Defined.

Global Instance Z_bin_op_is_assoc : IsAssoc (bin_op (A := Z)).
Proof. intros x y z. apply Z.add_assoc. Defined.

Global Instance Z_bin_op_is_semigrp : IsSemigrp (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_is_comm : IsComm (bin_op (A := Z)).
Proof. intros x y. apply Z.add_comm. Defined.

Global Instance Z_bin_op_null_op_is_unl_l : IsUnlL null_op (bin_op (A := Z)).
Proof. intros x. apply Z.add_0_l. Defined.

Global Instance Z_bin_op_null_op_is_unl_r : IsUnlR null_op (bin_op (A := Z)).
Proof. intros x. apply Z.add_0_r. Defined.

Global Instance Z_bin_op_null_op_is_unl : IsUnlLR null_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_mon : IsMon null_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_un_op_is_inv_l_hom :
  IsInvL null_op un_op (bin_op (A := Z)).
Proof. intros x. apply Z.add_opp_diag_l. Defined.

Global Instance Z_bin_op_null_op_un_op_is_inv_r_hom :
  IsInvR null_op un_op (bin_op (A := Z)).
Proof. intros x. apply Z.add_opp_diag_r. Defined.

Global Instance Z_bin_op_null_op_un_op_is_inv_hom : IsInvLR null_op un_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_un_op_is_grp : IsGrp null_op un_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_un_op_is_ab_grp :
  IsAbGrp (bin_op (A := Z)) null_op un_op.
Proof. esplit; typeclasses eauto. Defined.

End Additive.

Module Multiplicative.

Global Instance Z_bin_op_has_bin_op : HasBinOp Z := Z.mul.
Global Instance Z_has_null_op : HasNullOp Z := Z.one.

Global Instance Z_bin_op_is_mag : IsMag eq (bin_op (A := Z)).
Proof. hnf. typeclasses eauto. Defined.

Global Instance Z_bin_op_is_assoc : IsAssoc (bin_op (A := Z)).
Proof. intros x y z. apply Z.mul_assoc. Defined.

Global Instance Z_bin_op_is_semigrp : IsSemigrp (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_is_comm : IsComm (bin_op (A := Z)).
Proof. intros x y. apply Z.mul_comm. Defined.

Global Instance Z_bin_op_null_op_is_unl_l : IsUnlL null_op (bin_op (A := Z)).
Proof. intros x. apply Z.mul_1_l. Defined.

Global Instance Z_bin_op_null_op_is_unl_r : IsUnlR null_op (bin_op (A := Z)).
Proof. intros x. apply Z.mul_1_r. Defined.

Global Instance Z_bin_op_null_op_is_unl : IsUnlLR null_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_bin_op_null_op_is_mon : IsMon null_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Defined.

End Multiplicative.

Global Instance Z_has_add : HasAdd Z := Z.add.
Global Instance Z_has_zero : HasZero Z := Z.zero.
Global Instance Z_has_neg : HasNeg Z := Z.opp.
Global Instance Z_has_mul : HasMul Z := Z.mul.
Global Instance Z_has_one : HasOne Z := Z.one.

Global Instance Z_add_is_comm : IsComm add.
Proof. intros x y. apply Z.add_comm. Defined.

Global Instance Z_add_mul_is_distr_l : IsDistrL mul add.
Proof. intros x y z. apply Z.mul_add_distr_l. Defined.

Global Instance Z_add_mul_is_distr_r : IsDistrR mul add.
Proof. intros x y z. apply Z.mul_add_distr_r. Defined.

Global Instance Z_add_mul_is_distr : IsDistrLR mul add.
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_zero_mul_is_absorb_elem_l : IsAbsorbElemL zero mul.
Proof. intros x. apply Z.mul_0_l. Defined.

Global Instance Z_zero_mul_is_absorb_elem_r : IsAbsorbElemR zero mul.
Proof. intros x. apply Z.mul_0_r. Defined.

Global Instance Z_zero_mul_is_absorb_elem_l_r : IsAbsorbElemLR zero mul.
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_zero_add_one_mul_is_semiring : IsSemiring zero add one mul.
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_zero_neg_add_one_mul_is_ring : IsRing zero neg add one mul.
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_mul_is_comm : IsComm mul.
Proof. intros x y. apply Z.mul_comm. Defined.

(** TODO Organize the rest. *)

Global Instance Z_has_eq_rel : HasEqRel Z := Z.eq.

Global Instance Z_eq_is_refl : IsRefl Z.eq.
Proof. intros x. reflexivity. Defined.

Global Instance Z_eq_is_sym : IsSym Z.eq.
Proof. intros x y p. symmetry; auto. Defined.

Global Instance Z_eq_is_trans : IsTrans Z.eq.
Proof. intros x y z p q. transitivity y; auto. Defined.

Global Instance Z_eq_is_part_eq : IsPartEq Z.eq.
Proof. esplit; typeclasses eauto. Defined.

Global Instance Z_eq_is_eq : IsEq Z.eq.
Proof. esplit; typeclasses eauto. Defined.

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

Global Instance Z_N_is_iso_l_r : IsIsoLR Z_to_double_N Z_of_double_N.
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
