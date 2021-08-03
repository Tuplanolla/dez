(** * Distance Monoid or Generalized Metric Space *)

From Maniunfold.Has Require Export
  NullaryOperation BinaryOperation OrderRelations Distance.
From Maniunfold.Is Require Export
  TotalOrder Bounded Monoid Commutative Monotonic.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations AdditiveNotations.

(** This generalization was thoroughly investigated by Gabe Conant. *)

Class IsDistMon (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_tot_ord :> IsTotOrd _<=_;
  is_lower_bnd :> IsLowerBnd 0 _<=_;
  is_mon :> IsMon 0 _+_;
  is_comm :> IsCommBinOp _+_;
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
}.

Module Alternative.

(** This generalization was thoroughly investigated by Matěj Konečný. *)

Class IsPartOrdCommSemigrp (A : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A) : Prop := {
  is_part_ord :> IsPartOrd _<=_;
  is_refl :> IsRefl _<=_;
  some_property_l (x y : A) : x <= x + y;
  (* some_property_r (x y : A) : y <= x + y; *)
  is_semigrp :> IsSemigrp _+_;
  is_comm :> IsCommBinOp _+_;
  is_mono_bin_op :> IsMonoBinOp _<=_ _+_;
}.

End Alternative.

Class IsMetric (A B : Type)
  (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) : Prop := {
  is_dist_mon :> IsDistMon _<=_ 0 _+_;
  triangle (x y z : B) : dist x z <= dist x y + dist y z;
}.

(** TODO Commutative torsors here? *)

Class IsCommBinOp' (A B : Type) (Hd : HasDist A B) : Prop :=
  comm_bin_op' (x y : B) : dist x y = dist y x.

Section Context.

Context (A B : Type) (HR : HasOrdRel A) (Hx : HasNullOp A) (Hk : HasBinOp A)
  (Hd : HasDist A B) `(!IsMetric _<=_ 0 _+_ dist).

#[local] Instance is_comm' : IsCommBinOp' dist.
Proof. intros x y. Abort.

(** Also [0 <= dist x y] and [dist x y = 0 <-> x = y]. *)

End Context.
