(** * Metric Space *)

From Coq Require Import
  Lia Reals.Reals.
From DEZ.Has Require Export
  Operations OrderRelations Distances ArithmeticOperations.
From DEZ.Is Require Export
  Subrelation Subadditive
  TotalOrder Bounded Monoid Commutative Monotonic Inflationary.
From DEZ.Supports Require Import
  OrderNotations AdditiveNotations ArithmeticNotations.

Class IsNonnegForm (A B : Type) (X : A -> A -> Prop)
  (x : A) (s : B -> B -> A) : Prop :=
  nonneg_form (a b : B) : X x (s a b).

Module Real.

#[local] Open Scope R_scope.

(** TODO Put these in some real theorem module. *)

#[export] Instance R_has_equiv_rel : HasEquivRel R := _=_.
#[export] Instance R_has_ord_rel : HasOrdRel R := Rle.
#[export] Instance R_has_zero : HasZero R := R0.
#[export] Instance R_has_add : HasAdd R := Rplus.
#[export] Instance R_has_one : HasOne R := R1.
#[export] Instance R_has_mul : HasMul R := Rmult.

Class IsNonnegForm (B : Type)
  (s : B -> B -> R) : Prop :=
  nonneg_form (a b : B) : 0 <= s a b.

(** ** Metric Space *)

(** This is the usual definition in the setoid model. *)

Class IsMetric (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) : Prop := {
  metric_is_equiv :> IsEquiv X;
  metric_is_iff_rel :> IsIffRel X (fun a b : B => d a b = 0);
  metric_is_comm_form :> IsCommForm _=_ d;
  metric_is_subadd :> IsSubadd Rle Rplus d;
  (* metric_is_subadd :> IsSubadd _<=_ _+_ d; *)
  metric_is_proper :> IsProper (X ==> X ==> _=_) d;
}.

Section Context.

Context (B : Type) (X : B -> B -> Prop)
  (d : B -> B -> R) `{!IsMetric X d}.

#[local] Notation "'|' y '-' x '|'" := (dist x y) (format "'|' y  '-'  x '|'").

#[local] Lemma metric_is_nonneg : IsNonnegForm d.
Proof.
  assert (r : forall a : B, d a a = 0).
  { intros a. apply metric_is_iff_rel. reflexivity. }
  intros a b.
  apply (Rmult_le_reg_r 2).
  - apply IZR_lt. lia.
  - rewrite Rmult_0_l.
    replace 2%Z with (Z.succ 1)%Z by lia.
    rewrite succ_IZR. rewrite Rmult_plus_distr_l. rewrite Rmult_1_r.
    replace (d a b) with (d b a) at 2 by apply comm_form.
    erewrite <- r. apply subadd. Qed.

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
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
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
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
}.

End Alternative.

Class IsMetric (A B : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) : Prop := {
  is_dist_mon :> IsDistMon _<=_ 0 _+_;
  is_subadd :> IsSubadd _<=_ _+_ dist;
}.

Section Context.

Context (A B : Type) (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) `{!IsMetric _<=_ 0 _+_ dist}.

#[local] Notation "'|' y '-' x '|'" := (dist x y) (format "'|' y  '-'  x '|'").

#[local] Instance is_comm_tor_l : IsCommForm _=_ dist.
Proof.
  intros x y.
  pose proof subadd x y x as b.
  pose proof connex (X := _<=_) (dist x y) (dist y x) as [a | a];
  change bin_rel with _<=_ in a. Abort.

(** Also [0 <= dist x y] and [dist x y = 0 <-> x = y]. *)

End Context.
