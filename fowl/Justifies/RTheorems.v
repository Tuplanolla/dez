(** * Properties of Synthetic Real Numbers *)

From Coq Require Import
  Lia Reals.Reals.
From DEZ.Has Require Export
  EquivalenceRelations OrderRelations
  Operations ArithmeticOperations Distances.
From DEZ.Is Require Export
  TotalOrder Group (* Field *) Ring.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations AdditiveNotations ArithmeticNotations.

#[local] Open Scope R_scope.

(** ** Notations Missing from the Standard Library *)

Notation "'_<=_'" := Rle : R_scope.
Notation "x '<=' y" := (Rle x y) : R_scope.

Notation "'_+_'" := Rplus : R_scope.
Notation "x '+' y" := (Rplus x y) : R_scope.

Notation "'-_'" := Ropp : R_scope.
Notation "'-' x" := (Ropp x) : R_scope.

Notation "'_-_'" := Rminus : R_scope.
Notation "y '-' x" := (Rminus y x) : R_scope.

Notation "'_*_'" := Rmult : R_scope.
Notation "x '*' y" := (Rmult x y) : R_scope.

Notation "'/_'" := Rinv : R_scope.
Notation "'/' x" := (Rinv x) : R_scope.

Notation "'_/_'" := Rdiv : R_scope.
Notation "y '/' x" := (Rdiv y x) : R_scope.

Ltac ecrush :=
  repeat (try typeclasses eauto; esplit);
  hnf in *; eauto with real rorders.

(** ** Total Ordering *)

#[export] Instance R_has_equiv_rel : HasEquivRel R := _=_.
#[export] Instance R_has_ord_rel : HasOrdRel R := Rle.

#[export] Instance Rle_is_refl : IsRefl Rle.
Proof. ecrush. Qed.

#[export] Instance Rle_is_trans : IsTrans Rle.
Proof. exact Rle_trans. Qed.

#[export] Instance Rle_is_connex : IsConnex Rle.
Proof.
  intros x y.
  pose proof Rle_or_lt x y as a.
  pose proof Rlt_le y x as b.
  intuition. Qed.

#[export] Instance Rle_is_preord : IsPreord Rle.
Proof. ecrush. Qed.

#[export] Instance Rle_is_antisym : IsAntisym _=_ Rle.
Proof. exact Rle_antisym. Qed.

#[export] Instance Rle_is_part_ord : IsPartOrd _=_ Rle.
Proof. ecrush. Qed.

#[export] Instance Rle_is_tot_ord : IsTotOrd _=_ Rle.
Proof. ecrush. Qed.

(** ** Additive Group *)

Module Additive.

#[export] Instance R_has_null_op : HasNullOp R := 0.
#[export] Instance R_has_un_op : HasUnOp R := Ropp.
#[export] Instance R_has_bin_op : HasBinOp R := Rplus.

End Additive.

#[export] Instance R_add_is_assoc : IsAssoc _=_ Rplus.
Proof. ecrush. Qed.

#[export] Instance R_add_is_semigrp : IsSemigrp _=_ Rplus.
Proof. ecrush. Qed.

#[local] Instance R_add_is_unl_elem_l : IsUnlElemL _=_ 0 Rplus.
Proof. ecrush. Qed.

#[local] Instance R_add_is_unl_elem_r : IsUnlElemR _=_ 0 Rplus.
Proof. ecrush. Qed.

#[export] Instance R_add_is_unl_elem : IsUnlElem _=_ 0 Rplus.
Proof. ecrush. Qed.

#[export] Instance R_add_is_mon : IsMon _=_ 0 Rplus.
Proof. ecrush. Qed.

#[local] Instance R_add_is_inv_l : IsInvL _=_ 0 Ropp Rplus.
Proof. ecrush. Qed.

#[local] Instance R_add_is_inv_r : IsInvR _=_ 0 Ropp Rplus.
Proof. ecrush. Qed.

#[export] Instance R_add_is_inv : IsInv _=_ 0 Ropp Rplus.
Proof. ecrush. Qed.

#[export] Instance R_add_is_grp : IsGrp _=_ 0 Ropp Rplus.
Proof. ecrush. Qed.

#[export] Instance R_add_is_comm_bin_op : IsCommBinOp _=_ Rplus.
Proof. ecrush. Qed.

(** ** Multiplicative Group *)

Module Multiplicative.

#[export] Instance R_has_null_op : HasNullOp R := 1.
#[export] Instance R_has_un_op : HasUnOp R := Rinv.
#[export] Instance R_has_bin_op : HasBinOp R := Rmult.

End Multiplicative.

#[export] Instance R_mul_is_assoc : IsAssoc _=_ Rmult.
Proof. ecrush. Qed.

#[export] Instance R_mul_is_semigrp : IsSemigrp _=_ Rmult.
Proof. ecrush. Qed.

#[local] Instance R_mul_is_unl_elem_l : IsUnlElemL _=_ 1 Rmult.
Proof. ecrush. Qed.

#[local] Instance R_mul_is_unl_elem_r : IsUnlElemR _=_ 1 Rmult.
Proof. ecrush. Qed.

#[export] Instance R_mul_is_unl_elem : IsUnlElem _=_ 1 Rmult.
Proof. ecrush. Qed.

#[export] Instance R_mul_is_mon : IsMon _=_ 1 Rmult.
Proof. ecrush. Qed.

(* #[local] Instance R_mul_is_inv_l : IsInvL _=_ 1 Rinv Rmult.
Proof. ecrush. Qed.

#[local] Instance R_mul_is_inv_r : IsInvR _=_ 1 Rinv Rmult.
Proof. ecrush. Qed.

#[export] Instance R_mul_is_inv : IsInv _=_ 1 Rinv Rmult.
Proof. ecrush. Qed.

#[export] Instance R_mul_is_grp : IsGrp _=_ 1 Rinv Rmult.
Proof. ecrush. Qed. *)

#[export] Instance R_mul_is_comm_bin_op : IsCommBinOp _=_ Rmult.
Proof. ecrush. Qed.

(** ** Field *)

#[export] Instance R_has_zero : HasZero R := 0.
#[export] Instance R_has_neg : HasNeg R := Ropp.
#[export] Instance R_has_add : HasAdd R := Rplus.
#[export] Instance R_has_one : HasOne R := 1.
#[export] Instance R_has_recip : HasRecip R := Rinv.
#[export] Instance R_has_mul : HasMul R := Rmult.
#[export] Instance R_has_dist : HasDist R R := R_dist.

#[local] Instance R_is_distr_l : IsDistrL _=_ Rmult Rplus.
Proof. exact Rmult_plus_distr_l. Qed.

#[local] Instance R_is_distr_r : IsDistrR _=_ Rmult Rplus.
Proof. exact Rmult_plus_distr_r. Qed.

#[export] Instance R_is_distr : IsDistr _=_ Rmult Rplus.
Proof. ecrush. Qed.

#[export] Instance R_is_ring : IsRing _=_ 0 Ropp Rplus 1 Rmult.
Proof. ecrush. Qed.
