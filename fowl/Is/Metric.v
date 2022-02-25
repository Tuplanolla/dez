(** * Metric Space *)

From Coq Require Import
  Reals.Reals.
From DEZ.Has Require Export
  NullaryOperation BinaryOperation OrderRelations Distance.
From DEZ.Is Require Export
  Indiscernible Subadditive
  TotalOrder Bounded Monoid Commutative Monotonic Inflationary.
From DEZ.Supports Require Import
  OrderRelationNotations AdditiveNotations.

Module Real.

(** ** Real Metric Space *)

(** This is the usual definition in the setoid model. *)

Class IsRMetric (A : Type) (X : A -> A -> Prop) (Y : R -> R -> Prop)
  (d : A -> A -> R) : Prop := {
  is_indisc :> IsIndisc Y X R0 d;
  is_comm :> IsComm Y d;
  is_subadd :> IsSubadd Rle Rplus d;
}.

End Real.

(** This generalization was thoroughly investigated by Gabe Conant. *)

Class IsDistMon (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_tot_ord :> IsTotOrd _=_ _<=_;
  is_lower_bnd :> IsLowerBnd 0 _<=_;
  is_mon :> IsMon _=_ 0 _+_;
  is_comm :> IsComm _=_ _+_;
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
}.

Module Alternative.

(** This generalization was thoroughly investigated by Matěj Konečný. *)

Class IsPartOrdCommSemigrp (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_part_ord :> IsPartOrd _=_ _<=_;
  is_refl :> IsRefl _<=_;
  is_infl_bin_op_l_r :> IsInflBinOpLR _<=_ _+_;
  is_semigrp :> IsSemigrp _=_ _+_;
  is_comm :> IsComm _=_ _+_;
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

#[local] Instance is_comm_tor_l : IsComm _=_ dist.
Proof.
  intros x y.
  unfold tor_l.
  pose proof subadd x y x as b.
  pose proof connex (X := _<=_) (dist x y) (dist y x) as [a | a];
  change bin_rel with _<=_ in a. Abort.

(** Also [0 <= dist x y] and [dist x y = 0 <-> x = y]. *)

End Context.
