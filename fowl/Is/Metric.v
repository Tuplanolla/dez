(** * Metric Space *)

From Coq Require Import
  Lia Reals.Reals.
From DEZ.Has Require Export
  Operations OrderRelations Forms Distances ArithmeticOperations.
From DEZ.Is Require Export
  Equivalence Commutative Toeplitz Nonnegative Subadditive Subrelation
  TotalOrder Bounded Monoid Monotonic Inflationary.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations AdditiveNotations ArithmeticNotations.

#[local] Notation "'|' y '-' x '|'" := (dist x y) (format "'|' y  '-'  x '|'").

Module Real.

(** TODO Put these in some real theorems module. *)

#[local] Open Scope R_scope.

#[local] Notation "'_<=_'" := Rle : R_scope.
#[local] Notation "x '<=' y" := (Rle x y) : R_scope.

#[local] Notation "'_+_'" := Rplus : R_scope.
#[local] Notation "x '+' y" := (Rplus x y) : R_scope.

#[local] Notation "'-_'" := Ropp : R_scope.
#[local] Notation "'-' x" := (Ropp x) : R_scope.

#[local] Notation "'_-_'" := Rminus : R_scope.
#[local] Notation "y '-' x" := (Rminus y x) : R_scope.

#[local] Notation "'_*_'" := Rmult : R_scope.
#[local] Notation "x '*' y" := (Rmult x y) : R_scope.

#[local] Notation "'/_'" := Rinv : R_scope.
#[local] Notation "'/' x" := (Rinv x) : R_scope.

#[local] Notation "'_/_'" := Rdiv : R_scope.
#[local] Notation "y '/' x" := (Rdiv y x) : R_scope.

#[export] Instance R_has_equiv_rel : HasEquivRel R := _=_.
#[export] Instance R_has_ord_rel : HasOrdRel R := Rle.
#[export] Instance R_has_zero : HasZero R := R0.
#[export] Instance R_has_neg : HasNeg R := Ropp.
#[export] Instance R_has_add : HasAdd R := Rplus.
#[export] Instance R_has_one : HasOne R := R1.
#[export] Instance R_has_mul : HasMul R := Rmult.
#[export] Instance R_has_recip : HasRecip R := Rinv.

(** ** Real Pseudometric Space *)

Class IsRealPseudometric (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) : Prop := {
  real_pseudometric_is_equiv :> IsEquiv X;
  real_pseudometric_is_comm_form :> IsCommForm _=_ d;
  real_pseudometric_is_toeplitz_form :> IsToeplitzForm _=_ 0 d;
  real_pseudometric_is_nonneg_form :> IsNonnegForm _<=_ 0 d;
  real_pseudometric_is_subadd_form :> IsSubaddForm _<=_ _+_ d;
}.

(** ** Real Metric Space *)

Class IsRealMetric (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) : Prop := {
  real_metric_is_equiv :> IsEquiv X;
  real_metric_is_comm_form :> IsCommForm _=_ d;
  real_metric_is_iff_rel :> IsIffRel X (fun a b : B => d a b = 0);
  real_metric_is_subadd_form :> IsSubaddForm _<=_ _+_ d;
}.

Section Context.

Context (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) `{!IsRealMetric X d}.

#[local] Instance real_metric_has_equiv_rel : HasEquivRel B := X.

Ltac note := progress (
  try change X with (equiv_rel (A := B)) in *).

#[export] Instance real_metric_is_toeplitz_form : IsToeplitzForm _=_ 0 d.
Proof with note. intros a... apply real_metric_is_iff_rel. reflexivity. Qed.

#[export] Instance real_metric_is_nonneg_form : IsNonnegForm _<=_ 0 d.
Proof with note.
  intros a b... pose proof subadd_form a b a as s. rewrite toeplitz_form in s.
  apply (Rmult_le_reg_r 2).
  - apply IZR_lt. lia.
  - rewrite Rmult_0_l.
    replace 2%Z with (1 + 1)%Z by lia. rewrite plus_IZR.
    rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
    replace (d a b) with (d b a) at 2 by apply comm_form.
    apply s. Qed.

#[export] Instance real_metric_is_proper : IsProper (X ==> X ==> _=_) d.
Proof with note.
  intros a0 b0 s0 a1 b1 s1...
  pose proof (iff_rel_is_subrel (IsIffRel := real_metric_is_iff_rel)) as t.
  hnf in t. pose proof (t _ _ s0) as t0. pose proof (t _ _ s1) as t1.
  apply Rle_le_eq. split.
  - pose proof subadd_form a0 b0 a1 as u0.
    pose proof subadd_form b0 b1 a1 as u1.
    rewrite (comm_form a1 b1) in t1.
    rewrite t0 in u0. rewrite Rplus_0_l in u0.
    rewrite t1 in u1. rewrite Rplus_0_r in u1.
    eapply Rle_trans. apply u0. eapply Rle_trans. apply u1.
    apply Rle_refl.
  - pose proof subadd_form b0 a0 b1 as u0.
    pose proof subadd_form a0 a1 b1 as u1.
    rewrite (comm_form a0 b0) in t0.
    rewrite t0 in u0. rewrite Rplus_0_l in u0.
    rewrite t1 in u1. rewrite Rplus_0_r in u1.
    eapply Rle_trans. apply u0. eapply Rle_trans. apply u1.
    apply Rle_refl. Qed.

End Context.

End Real.

From DEZ.Supports Require Import
  OrderNotations ArithmeticNotations AdditiveNotations.

(** This generalization was thoroughly investigated by Gabe Conant. *)

Class IsDistMon (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_tot_ord :> IsTotOrd _=_ _<=_;
  is_lower_bnd :> IsLowerBnd _<=_ 0;
  is_mon :> IsMon _=_ 0 _+_;
  is_comm :> IsCommBinOp _=_ _+_;
  is_mono_bin_op :> IsMonoBinOpLR _<=_ _+_;
}.

Module Alternative.

(** This generalization was thoroughly investigated by Matěj Konečný. *)

Class IsPartOrdCommSemigrp (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_part_ord :> IsPartOrd _=_ _<=_;
  is_refl :> IsRefl _<=_;
  is_infl_bin_op_l_r :> IsInfl _<=_ _+_;
  is_semigrp :> IsSemigrp _=_ _+_;
  is_comm :> IsCommBinOp _=_ _+_;
  is_mono_bin_op :> IsMonoBinOpLR _<=_ _+_;
}.

End Alternative.

Class IsMetric (A B : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) : Prop := {
  is_dist_mon :> IsDistMon _<=_ 0 _+_;
  is_subadd_form :> IsSubaddForm _<=_ _+_ dist;
}.

Section Context.

Context (A B : Type) (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) `{!IsMetric _<=_ 0 _+_ dist}.

#[local] Notation "'|' y '-' x '|'" := (dist x y) (format "'|' y  '-'  x '|'").

#[local] Instance is_comm_tor_l : IsCommForm _=_ dist.
Proof.
  intros x y.
  pose proof subadd_form x y x as b.
  pose proof connex (X := _<=_) (dist x y) (dist y x) as [a | a];
  change bin_rel with _<=_ in a. Abort.

End Context.
