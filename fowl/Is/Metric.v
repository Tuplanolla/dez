(** * Distance Monoid or Generalized Metric Space *)

From Coq Require Import
  Reals.Reals.
From Maniunfold.Has Require Export
  NullaryOperation BinaryOperation OrderRelations Distance.
From Maniunfold.Is Require Export
  Indiscernible Subadditive
  TotalOrder Bounded Monoid Commutative Monotonic Inflationary.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations AdditiveNotations.

Module Classical.

(** This is the usual definition. *)

Class IsMetric (A : Type) (Hd : HasDist R A) : Prop := {
  is_indisc :> IsIndisc R0 dist;
  is_comm_tor_l :> IsCommTorL dist;
  is_subadd :> IsSubadd Rle Rplus dist;
}.

End Classical.

(** This generalization was thoroughly investigated by Gabe Conant. *)

Class IsDistMon (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_tot_ord :> IsTotOrd _<=_;
  is_lower_bnd :> IsLowerBnd 0 _<=_;
  is_mon :> IsMon 0 _+_;
  is_comm_bin_op :> IsCommBinOp _+_;
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
}.

Module Alternative.

(** This generalization was thoroughly investigated by Matěj Konečný. *)

Class IsPartOrdCommSemigrp (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_part_ord :> IsPartOrd _<=_;
  is_refl :> IsRefl _<=_;
  is_infl_bin_op_l_r :> IsInflBinOpLR _<=_ _+_;
  is_semigrp :> IsSemigrp _+_;
  is_comm_bin_op :> IsCommBinOp _+_;
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
  (Hd : HasDist A B) `(!IsMetric _<=_ 0 _+_ dist).

#[local] Instance is_comm_tor_l : IsCommTorL dist.
Proof.
  intros x y.
  unfold tor_l.
  pose proof subadd x y x as b.
  pose proof connex (HR := _<=_) (dist x y) (dist y x) as [a | a];
  change bin_rel with _<=_ in a. Abort.

(** Also [0 <= dist x y] and [dist x y = 0 <-> x = y]. *)

End Context.
