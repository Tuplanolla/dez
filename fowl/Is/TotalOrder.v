(** * Total Ordering *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations.
From DEZ.Is Require Export
  Connex PartialOrder Reflexive Antisymmetric Transitive Proper Irreflexive.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations.

(** ** Linear Order *)
(** ** Order *)
(** ** Total Order *)

Class IsTotOrd (A : Type) (Xeq Xle : A -> A -> Prop) : Prop := {
  tot_ord_is_connex :> IsConnex Xle;
  tot_ord_is_part_ord :> IsPartOrd Xeq Xle;
}.

Section Context.

Context (A : Type) (Xeq Xle : A -> A -> Prop).

#[local] Instance has_equiv_rel : HasEquivRel A := Xeq.
#[local] Instance has_ord_rel : HasOrdRel A := Xle.

Ltac note := progress (
  try change Xeq with (equiv_rel (A := A)) in *;
  try change Xle with (ord_rel (A := A)) in *).

(** Every total order is reflexive. *)

#[local] Instance tot_ord_is_refl
  `{!IsTotOrd Xeq Xle} : IsRefl Xle.
Proof. typeclasses eauto. Qed.

(** Every total order is antisymmetric. *)

#[local] Instance tot_ord_is_antisym
  `{!IsTotOrd Xeq Xle} : IsAntisym Xeq Xle.
Proof. typeclasses eauto. Qed.

(** Every total order is transitive. *)

#[local] Instance tot_ord_is_trans
  `{!IsTotOrd Xeq Xle} : IsTrans Xle.
Proof. typeclasses eauto. Qed.

End Context.

(** ** Strict Linear Order *)
(** ** Strict Order *)
(** ** Strict Total Order *)

Class IsStrTotOrd (A : Type) (Xeq Xle : A -> A -> Prop) : Prop := {
  str_tot_ord_is_connex :> IsConnex Xle;
  str_tot_ord_is_str_part_ord :> IsStrPartOrd Xle;
  str_tot_ord_is_proper :> IsProper (Xeq ==> Xeq ==> _<->_) Xle;
}.

Section Context.

Context (A : Type) (Xeq Xle : A -> A -> Prop).

(** Every strict total order is irreflexive. *)

#[local] Instance str_tot_ord_is_irrefl
  `{!IsStrTotOrd Xeq Xle} : IsIrrefl Xle.
Proof. typeclasses eauto. Qed.

(** Every strict total order is asymmetric. *)

#[local] Instance tot_ord_is_asym
  `{!IsStrTotOrd Xeq Xle} : IsAsym Xle.
Proof. typeclasses eauto. Qed.

(** Every strict total order is transitive. *)

#[local] Instance str_tot_ord_is_trans
  `{!IsStrTotOrd Xeq Xle} : IsTrans Xle.
Proof. typeclasses eauto. Qed.

End Context.
