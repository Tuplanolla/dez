(** * Distance Monoid or Generalized Metric Space *)

From Maniunfold.Has Require Export
  NullaryOperation BinaryOperation OrderRelations Distance.
From Maniunfold.Is Require Export
  Triangular TotalOrder Bounded Monoid Commutative Monotonic Inflationary.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations AdditiveNotations.

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
  is_triangle :> IsTriangle _<=_ _+_;
}.

Section Context.

Context (A B : Type) (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) `(!IsMetric _<=_ 0 _+_ dist).

#[local] Instance is_comm_tor_l : IsCommTorL dist.
Proof. intros x y. Abort.

(** Also [0 <= dist x y] and [dist x y = 0 <-> x = y]. *)

End Context.
