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
  EquivalenceNotations (* DistanceBarNotations *)
  OrderNotations AdditiveNotations ArithmeticNotations.

#[local] Open Scope R_scope.

(** TODO The rest is not in the diagram yet. *)

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
#[local] Instance real_pseudometric_has_dist : HasDist R B := d.

Ltac notations f := progress (
  f X (equiv_rel (A := B));
  f d (dist (A := R) (B := B))).

#[export] Instance real_pseudometric_is_proper :
  IsProper (X ==> X ==> _=_) d.
Proof with notations enabled.
  intros a0 b0 s0 a1 b1 s1...
  pose proof indisc_id_form a0 b0 s0 as t0.
  pose proof indisc_id_form a1 b1 s1 as t1.
  apply Rle_le_eq. split.
  - pose proof subadd_form a0 b0 a1 as u0.
    pose proof subadd_form b0 b1 a1 as u1.
    rewrite comm_form in t1.
    rewrite t0 in u0. rewrite unl_elem_l in u0.
    rewrite t1 in u1. rewrite unl_elem_r in u1.
    etransitivity.
    + apply u0.
    + etransitivity.
      * apply u1.
      * reflexivity.
  - pose proof subadd_form b0 a0 b1 as u0.
    pose proof subadd_form a0 a1 b1 as u1.
    rewrite comm_form in t0.
    rewrite t0 in u0. rewrite unl_elem_l in u0.
    rewrite t1 in u1. rewrite unl_elem_r in u1.
    etransitivity.
    + apply u0.
    + etransitivity.
      * apply u1.
      * reflexivity. Qed.

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
#[local] Instance real_metric_has_dist : HasDist R B := d.

Ltac notations f := progress (
  f X (equiv_rel (A := B));
  f d (dist (A := R) (B := B))).

#[export] Instance real_metric_is_toeplitz_form :
  IsToeplitzForm _=_ 0 d.
Proof with notations enabled.
  intros a... apply indisc_id_form. reflexivity. Qed.

#[export] Instance real_metric_is_nonneg_form :
  IsNonnegForm _<=_ 0 d.
Proof with notations enabled.
  intros a b...
  pose proof subadd_form a b a as s. rewrite toeplitz_form in s.
  apply (Rmult_le_reg_r 2).
  - apply IZR_lt. lia.
  - rewrite absorb_elem_l.
    replace 2%Z with (1 + 1)%Z by lia. rewrite plus_IZR.
    rewrite distr_l. rewrite unl_elem_r.
    rewrite (comm_form b a) in s.
    apply s. Qed.

#[export] Instance real_metric_is_real_pseudometric :
  IsRealPseudometric X d.
Proof. esplit; typeclasses eauto. Qed.

End Context.

#[export] Instance R_has_dist : HasDist R R := R_dist.

#[export] Instance R_dist_is_comm_form : IsCommForm _=_ R_dist.
Proof. intros x y. apply R_dist_sym. Qed.

#[export] Instance R_dist_is_subadd_form : IsSubaddForm _<=_ _+_ R_dist.
Proof. intros x y z. apply R_dist_tri. Qed.

#[export] Instance R_dist_is_indisc_id_form : IsIndiscIdForm _=_ _=_ 0 R_dist.
Proof. intros x y. apply R_dist_refl. Qed.

#[export] Instance R_dist_is_id_indisc_form : IsIdIndiscForm _=_ _=_ 0 R_dist.
Proof. intros x y. apply R_dist_refl. Qed.

#[export] Instance R_dist_is_real_metric : IsRealMetric _=_ R_dist.
Proof. esplit; typeclasses eauto. Qed.

Equations Rlt_eps (e : posreal) (x y : R) : Prop :=
  Rlt_eps e x y := Rlt x (e + y).

#[local] Instance Rlt_eps_wf (e : posreal) : WellFounded (Rlt_eps e).
Proof. Admitted.

Section Context.

Context (e : posreal).

Equations approach (x y : R) : R by wf (R_dist x y) (Rlt_eps e) :=
  approach x y with Rlt_le_dec (R_dist x y) e := {
    | left _ => y
    | right _ => approach x ((x + y) / 2)
  }.
Next Obligation.
  intros x y i rec.
  unfold R_dist.
  rewrite (Fdiv_def Rfield).
  rewrite distr_r.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite <- Rplus_assoc.
  rewrite (double_var x) at 1.
  rewrite (Rplus_assoc (x / 2)).
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  rewrite (Fdiv_def Rfield).
  unfold Rlt_eps.
  repeat match goal with
  | |- context c [?x + - ?y] => change (x + - y) with (x - y)
  (* | |- context c [?x * / ?y] => change (x * / y) with (x / y) *)
  end.
  rewrite (Rmult_comm x).
  rewrite (Rmult_comm y).
  repeat match goal with
  | |- context c [Rabs (?x - ?y)] => change (Rabs (x - y)) with (R_dist x y)
  end.
  rewrite R_dist_mult_l.
  rewrite Rabs_Rinv.
  2: { intros a. apply eq_IZR in a. lia. }
  rewrite <- abs_IZR. unfold Z.abs.
  Admitted.

Equations approach' (x y : R) : posreal :=
  approach' x y := mkposreal (approach x y) _.
Next Obligation. intros x y. Admitted.

End Context.

From Coq Require Import
  extraction.ExtrOcamlBasic extraction.Extraction
  extraction.ExtrOcamlNatBigInt Reals.ClassicalDedekindReals.

Extract Inductive posreal => "Float.t" [ "(fun x -> x)" ].
Extract Inductive negreal => "Float.t" [ "(fun x -> x)" ].
Extract Inductive nonnegreal => "Float.t" [ "(fun x -> x)" ].
Extract Inductive nonposreal => "Float.t" [ "(fun x -> x)" ].
Extract Constant pos => "(fun x -> x)".
Extract Constant neg => "(fun x -> x)".
Extract Constant nonneg => "(fun x -> x)".
Extract Constant nonpos => "(fun x -> x)".
Extract Constant DReal => "Float.t".
Extract Constant R => "Float.t".
Extract Constant RbaseSymbolsImpl.R => "Float.t".
Extract Inductive ConstructiveCauchyReals.CReal => "Unit.t" [ "()" ].
Extract Constant Rabst => "(fun _ -> 0.0)".
Extract Constant Rrepr => "(fun _ -> ())".
Extract Constant R0 => "Float.zero".
Extract Constant R1 => "Float.one".
Extract Constant Rabs => "Float.abs".
(* Extract Constant Rsqrt => "Float.sqrt". *)
Extract Constant Ropp => "Float.neg".
Extract Constant Rinv => "(Float.div Float.one)".
Extract Constant Req_EM_T => "(=)".
Extract Constant Req_appart_dec => "(=)".
Extract Constant Rlt_le_dec => "(<)".
Extract Constant Rle_lt_dec => "(<=)".
Extract Constant Rmult => "Float.mul".
Extract Constant Rplus => "Float.add".
Extract Constant Rminus => "Float.sub".
Extract Constant Rdiv => "Float.div".

Extraction "/tmp/metric.ml" approach'.

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
