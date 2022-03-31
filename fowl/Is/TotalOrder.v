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

Class IsTotOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  tot_ord_is_connex :> IsConnex Y;
  tot_ord_is_part_ord :> IsPartOrd X Y;
}.

Section Context.

Context (A : Type) (X Y : A -> A -> Prop).

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_ord_rel : HasOrdRel A := Y.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change Y with (ord_rel (A := A)) in *).

(** Every total order is reflexive. *)

#[local] Instance tot_ord_is_refl
  `{!IsTotOrd X Y} : IsRefl Y.
Proof. typeclasses eauto. Qed.

(** Every total order is antisymmetric. *)

#[local] Instance tot_ord_is_antisym
  `{!IsTotOrd X Y} : IsAntisym X Y.
Proof. typeclasses eauto. Qed.

(** Every total order is transitive. *)

#[local] Instance tot_ord_is_trans
  `{!IsTotOrd X Y} : IsTrans Y.
Proof. typeclasses eauto. Qed.

End Context.

(** ** Strict Linear Order *)
(** ** Strict Order *)
(** ** Strict Total Order *)

Class IsStrTotOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  str_tot_ord_is_connex :> IsConnex Y;
  str_tot_ord_is_str_part_ord :> IsStrPartOrd Y;
  str_tot_ord_is_proper :> IsProper (X ==> X ==> _<->_) Y;
}.

Section Context.

Context (A : Type) (X Y : A -> A -> Prop).

(** Every strict total order is irreflexive. *)

#[local] Instance str_tot_ord_is_irrefl
  `{!IsStrTotOrd X Y} : IsIrrefl Y.
Proof. typeclasses eauto. Qed.

(** Every strict total order is asymmetric. *)

#[local] Instance tot_ord_is_asym
  `{!IsStrTotOrd X Y} : IsAsym Y.
Proof. typeclasses eauto. Qed.

(** Every strict total order is transitive. *)

#[local] Instance str_tot_ord_is_trans
  `{!IsStrTotOrd X Y} : IsTrans Y.
Proof. typeclasses eauto. Qed.

End Context.
