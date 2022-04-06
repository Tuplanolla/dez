(** * Metric Spaces *)

From Coq Require Import
  Lia Reals.Reals.
From DEZ.Has Require Export
  Operations OrderRelations Forms Distances ArithmeticOperations.
From DEZ.Is Require Export
  Equivalence Commutative Toeplitz Nonnegative Subadditive Indiscernible
  TotalOrder Bounded Monoid Monotonic Inflationary.
From DEZ.Justifies Require Export
  RTheorems.
From DEZ.Provides Require Import
  TypeclassTactics.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations AdditiveNotations ArithmeticNotations.

#[local] Open Scope R_scope.

#[local] Notation "'|' y '-' x '|'" := (dist x y) (format "'|' y  '-'  x '|'").

(** ** Real Pseudometric Space *)

Class IsRealPseudometric (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) : Prop := {
  real_pseudometric_is_equiv :> IsEquiv X;
  real_pseudometric_is_comm_form :> IsCommForm _=_ d;
  real_pseudometric_is_toeplitz_form :> IsToeplitzForm _=_ 0 d;
  real_pseudometric_is_nonneg_form :> IsNonnegForm _<=_ 0 d;
  real_pseudometric_is_subadd_form :> IsSubaddForm _<=_ _+_ d;
  real_pseudometric_is_indisc_id_form :> IsIndiscIdForm _=_ X 0 d;
}.

Section Context.

Context (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) `{!IsRealPseudometric X d}.

#[local] Instance real_pseudometric_has_equiv_rel : HasEquivRel B := X.

Ltac note := progress (
  denote X with (equiv_rel (A := B))).

#[export] Instance real_pseudometric_is_proper : IsProper (X ==> X ==> _=_) d.
Proof with note.
  intros a0 b0 s0 a1 b1 s1...
  pose proof indisc_id_form a0 b0 s0 as t0.
  pose proof indisc_id_form a1 b1 s1 as t1.
  apply Rle_le_eq. split.
  - pose proof subadd_form a0 b0 a1 as u0.
    pose proof subadd_form b0 b1 a1 as u1.
    rewrite comm_form in t1.
    rewrite t0 in u0. rewrite unl_elem_l in u0.
    rewrite t1 in u1. rewrite unl_elem_r in u1.
    etransitivity. apply u0. etransitivity. apply u1. reflexivity.
  - pose proof subadd_form b0 a0 b1 as u0.
    pose proof subadd_form a0 a1 b1 as u1.
    rewrite comm_form in t0.
    rewrite t0 in u0. rewrite unl_elem_l in u0.
    rewrite t1 in u1. rewrite unl_elem_r in u1.
    etransitivity. apply u0. etransitivity. apply u1. reflexivity. Qed.

End Context.

(** ** Real Metric Space *)

Class IsRealMetric (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) : Prop := {
  real_metric_is_equiv :> IsEquiv X;
  real_metric_is_comm_form :> IsCommForm _=_ d;
  real_metric_is_subadd_form :> IsSubaddForm _<=_ _+_ d;
  real_metric_is_indisc_id_form :> IsIndiscIdForm _=_ X 0 d;
  real_metric_is_id_indisc_form :> IsIdIndiscForm _=_ X 0 d;
}.

Section Context.

Context (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) `{!IsRealMetric X d}.

#[local] Instance real_metric_has_equiv_rel : HasEquivRel B := X.

Ltac note := progress (
  denote X with (equiv_rel (A := B))).

#[export] Instance real_metric_is_toeplitz_form : IsToeplitzForm _=_ 0 d.
Proof with note.
  intros a... apply indisc_id_form. reflexivity. Qed.

#[export] Instance real_metric_is_nonneg_form : IsNonnegForm _<=_ 0 d.
Proof with note.
  intros a b... pose proof subadd_form a b a as s. rewrite toeplitz_form in s.
  apply (Rmult_le_reg_r 2).
  - apply IZR_lt. lia.
  - rewrite absorb_elem_l.
    replace 2%Z with (1 + 1)%Z by lia. rewrite plus_IZR.
    rewrite distr_l. rewrite unl_elem_r.
    rewrite (comm_form b a) in s.
    apply s. Qed.

#[export] Instance real_metric_is_real_pseudometric : IsRealPseudometric X d.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** TODO The rest! *)

From DEZ.Supports Require Import
  OrderNotations ArithmeticNotations AdditiveNotations.

(** This generalization was thoroughly investigated by Gabe Conant. *)

Class IsDistMon (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_tot_ord :> IsTotOrd _=_ _<=_;
  is_lower_bnd :> IsLowerBnd _<=_ 0;
  is_mon :> IsMon _=_ 0 _+_;
  is_comm_bin_op :> IsCommBinOp _=_ _+_;
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
}.

Module Alternative.

(** This generalization was thoroughly investigated by Matěj Konečný. *)

Class IsPartOrdCommSemigrp (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_part_ord :> IsPartOrd _=_ _<=_;
  is_refl :> IsRefl _<=_;
  is_infl :> IsInfl _<=_ _+_;
  is_semigrp :> IsSemigrp _=_ _+_;
  is_comm_bin_op :> IsCommBinOp _=_ _+_;
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
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

#[local] Instance is_comm_tor_l : IsCommForm _=_ dist.
Proof.
  intros x y.
  pose proof subadd_form x y x as b.
  pose proof connex (X := _<=_) (dist x y) (dist y x) as [a | a];
  change bin_rel with _<=_ in a. Abort.

End Context.
