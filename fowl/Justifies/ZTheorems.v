(** Properties of Binary Integers *)

From Coq Require Import
  ZArith.ZArith.
From DEZ.Has Require Export
  EquivalenceRelations Decisions OrderRelations
  Operations ArithmeticOperations.
From DEZ.Is Require Export
  TotalOrder Group Ring Isomorphic.

#[local] Open Scope Z_scope.

Ltac ecrush :=
  repeat (try typeclasses eauto; esplit);
  hnf in *; eauto with zarith.

(** ** Decidable Total Ordering *)

#[export] Instance Z_has_equiv_rel : HasEquivRel Z := _=_.
#[export] Instance Z_has_equiv_dec : HasEquivDec Z := Z.eq_dec.
#[export] Instance Z_has_ord_rel : HasOrdRel Z := Z.le.

#[export] Instance Z_le_is_refl : IsRefl Z.le.
Proof. ecrush. Qed.

#[export] Instance Z_le_is_trans : IsTrans Z.le.
Proof. ecrush. Qed.

#[export] Instance Z_le_is_connex : IsConnex Z.le.
Proof.
  intros x y.
  pose proof Z.le_gt_cases x y as a.
  pose proof Z.lt_le_incl y x as b.
  intuition.
Qed.

#[export] Instance Z_le_is_preord : IsPreord Z.le.
Proof. ecrush. Qed.

#[export] Instance Z_le_is_antisym : IsAntisym _=_ Z.le.
Proof. ecrush. Qed.

#[export] Instance Z_le_is_part_ord : IsPartOrd _=_ Z.le.
Proof. ecrush. Qed.

#[export] Instance Z_le_is_tot_ord : IsTotOrd _=_ Z.le.
Proof. ecrush. Qed.

(** ** Additive Group *)

Module Additive.

#[export] Instance Z_has_null_op : HasNullOp Z := 0.
#[export] Instance Z_has_un_op : HasUnOp Z := Z.opp.
#[export] Instance Z_has_bin_op : HasBinOp Z := Z.add.

End Additive.

#[export] Instance Z_add_is_assoc : IsAssoc _=_ Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_add_is_semigrp : IsSemigrp _=_ Z.add.
Proof. ecrush. Qed.

#[local] Instance Z_add_is_unl_elem_l : IsUnlElemL _=_ 0 Z.add.
Proof. ecrush. Qed.

#[local] Instance Z_add_is_unl_elem_r : IsUnlElemR _=_ 0 Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_add_is_unl_elem : IsUnlElem _=_ 0 Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_add_is_mon : IsMon _=_ 0 Z.add.
Proof. ecrush. Qed.

#[local] Instance Z_add_is_inv_l : IsInvL _=_ 0 Z.opp Z.add.
Proof. ecrush. Qed.

#[local] Instance Z_add_is_inv_r : IsInvR _=_ 0 Z.opp Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_add_is_inv : IsInv _=_ 0 Z.opp Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_add_is_grp : IsGrp _=_ 0 Z.opp Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_add_is_comm_bin_op : IsCommBinOp _=_ Z.add.
Proof. ecrush. Qed.

(** ** Multiplicative Group *)

Module Multiplicative.

#[export] Instance Z_has_null_op : HasNullOp Z := 1.
#[export] Instance Z_has_bin_op : HasBinOp Z := Z.mul.

End Multiplicative.

#[export] Instance Z_mul_is_assoc : IsAssoc _=_ Z.mul.
Proof. ecrush. Qed.

#[export] Instance Z_mul_is_semigrp : IsSemigrp _=_ Z.mul.
Proof. ecrush. Qed.

#[local] Instance Z_mul_is_unl_elem_l : IsUnlElemL _=_ 1 Z.mul.
Proof. ecrush. Qed.

#[local] Instance Z_mul_is_unl_elem_r : IsUnlElemR _=_ 1 Z.mul.
Proof. ecrush. Qed.

#[export] Instance Z_mul_is_unl_elem : IsUnlElem _=_ 1 Z.mul.
Proof. ecrush. Qed.

#[export] Instance Z_mul_is_mon : IsMon _=_ 1 Z.mul.
Proof. ecrush. Qed.

#[export] Instance Z_mul_is_comm_bin_op : IsCommBinOp _=_ Z.mul.
Proof. ecrush. Qed.

(** ** Ring *)

#[export] Instance Z_has_zero : HasZero Z := 0.
#[export] Instance Z_has_neg : HasNeg Z := Z.opp.
#[export] Instance Z_has_add : HasAdd Z := Z.add.
#[export] Instance Z_has_one : HasOne Z := 1.
#[export] Instance Z_has_mul : HasMul Z := Z.mul.

#[local] Instance Z_is_distr_l : IsDistrL _=_ Z.mul Z.add.
Proof. ecrush. Qed.

#[local] Instance Z_is_distr_r : IsDistrR _=_ Z.mul Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_is_distr : IsDistr _=_ Z.mul Z.add.
Proof. ecrush. Qed.

#[export] Instance Z_is_ring : IsRing _=_ 0 Z.opp Z.add 1 Z.mul.
Proof. ecrush. Qed.

(** ** Sign--Parity Isomorphism *)

Equations Z_to_double_N (n : Z) : N :=
  Z_to_double_N Z0 := N0;
  Z_to_double_N (Zpos p) := Npos (xO p);
  Z_to_double_N (Zneg p) := Npos (Pos.pred_double p).

Equations Z_of_double_N (n : N) : Z :=
  Z_of_double_N N0 := Z0;
  Z_of_double_N (Npos (xI q)) := Zneg (Pos.succ q);
  Z_of_double_N (Npos (xO q)) := Zpos q;
  Z_of_double_N (Npos xH) := Zneg xH.

#[local] Instance is_retr : IsRetr _=_ Z_to_double_N Z_of_double_N.
Proof.
  intros x. destruct x as [| p | p].
  - reflexivity.
  - reflexivity.
  - destruct p as [q | q |].
    + reflexivity.
    + cbn. rewrite (Pos.succ_pred_double q). reflexivity.
    + reflexivity.
Qed.

#[local] Instance is_sect : IsSect _=_ Z_to_double_N Z_of_double_N.
Proof.
  intros x. destruct x as [| p].
  - reflexivity.
  - destruct p as [q | q |].
    + cbn. rewrite (Pos.pred_double_succ q). reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

#[export] Instance is_iso : IsIso _=_ _=_ Z_to_double_N Z_of_double_N.
Proof. ecrush. Qed.
