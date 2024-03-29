(** * Total Ordering *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations.
From DEZ.Is Require Export
  Connex PartialOrder Reflexive Antisymmetric Transitive Proper Irreflexive.
From DEZ.Provides Require Import
  TypeclassTactics.
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
  denote Xeq with (equiv_rel (A := A));
  denote Xle with (ord_rel (A := A))).

(** A total order is reflexive. *)

#[local] Instance tot_ord_is_refl
  `{!IsTotOrd Xeq Xle} : IsRefl Xle.
Proof. typeclasses eauto. Qed.

(** A total order is antisymmetric. *)

#[local] Instance tot_ord_is_antisym
  `{!IsTotOrd Xeq Xle} : IsAntisym Xeq Xle.
Proof. typeclasses eauto. Qed.

(** A total order is transitive. *)

#[local] Instance tot_ord_is_trans
  `{!IsTotOrd Xeq Xle} : IsTrans Xle.
Proof. typeclasses eauto. Qed.

End Context.

(** ** Strict Linear Order *)
(** ** Strict Order *)
(** ** Strict Total Order *)

Class IsStrTotOrd (A : Type) (Xeq Xlt : A -> A -> Prop) : Prop := {
  str_tot_ord_is_str_part_ord :> IsStrPartOrd Xlt;
  str_tot_ord_is_str_connex :> IsStrConnex Xeq Xlt;
  str_tot_ord_is_proper :> IsProper (Xeq ==> Xeq ==> _<->_) Xlt;
}.

Section Context.

Context (A : Type) (Xeq Xlt : A -> A -> Prop).

(** A strict total order is irreflexive. *)

#[local] Instance str_tot_ord_is_irrefl
  `{!IsStrTotOrd Xeq Xlt} : IsIrrefl Xlt.
Proof. typeclasses eauto. Qed.

(** A strict total order is asymmetric. *)

#[local] Instance tot_ord_is_asym
  `{!IsStrTotOrd Xeq Xlt} : IsAsym Xlt.
Proof. typeclasses eauto. Qed.

(** A strict total order is transitive. *)

#[local] Instance str_tot_ord_is_trans
  `{!IsStrTotOrd Xeq Xlt} : IsTrans Xlt.
Proof. typeclasses eauto. Qed.

End Context.
