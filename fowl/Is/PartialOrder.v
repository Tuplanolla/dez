(** * Partial Ordering *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations.
From DEZ.Is Require Export
  Equivalence Preorder Antisymmetric Proper Irreflexive Transitive Asymmetric.
From DEZ.Provides Require Import
  TypeclassTactics.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations.

#[local] Existing Instance antisymmetric_is_antisym.

(** ** Partial Order *)

(** We cannot define [IsPartOrd] as a notation for [PartialOrder],
    because [PartialOrder] is constrained by [Equivalence] and [PreOrder] and
    built from [relation_equivalence]. *)

Fail Fail Notation IsPartOrd := PartialOrder.

Class IsPartOrd (A : Type) (Xeq Xle : A -> A -> Prop) : Prop := {
  part_ord_is_equiv :> IsEquiv Xeq;
  part_ord_is_preord :> IsPreord Xle;
  part_ord_is_antisym :> IsAntisym Xeq Xle;
  part_ord_is_proper :> IsProper (Xeq ==> Xeq ==> _<->_) Xle;
}.

Section Context.

Context (A : Type) (Xeq Xle : A -> A -> Prop).

#[local] Instance has_equiv_rel : HasEquivRel A := Xeq.
#[local] Instance has_ord_rel : HasOrdRel A := Xle.

Ltac note := progress (
  denote Xeq with (equiv_rel (A := A));
  denote Xle with (ord_rel (A := A))).

(** Standard library partial order implies our partial order. *)

#[local] Instance partial_order_is_part_ord
  `{!Equivalence Xeq} `{!PreOrder Xle} `{!PartialOrder Xeq Xle} :
  IsPartOrd Xeq Xle.
Proof. esplit; typeclasses eauto. Qed.

(** Our partial order implies standard library partial order. *)

#[local] Instance part_ord_partial_order
  `{!IsPartOrd Xeq Xle} : PartialOrder Xeq Xle.
Proof.
  note. intros x y. unfold pointwise_lifting, relation_conjunction.
  unfold predicate_intersection. unfold pointwise_extension. unfold flip.
  pose proof antisym x y as a.
  pose proof fun a : x == y => part_ord_is_proper x x id x y a as b.
  pose proof fun a : x == y => part_ord_is_proper y y id y x (a ^-1) as c.
  intuition. Qed.

(** A partial order is reflexive. *)

#[local] Instance part_ord_is_refl
  `{!IsPartOrd Xeq Xle} : IsRefl Xle.
Proof. typeclasses eauto. Qed.

(** A partial order is transitive. *)

#[local] Instance part_ord_is_trans
 `{!IsPartOrd Xeq Xle} : IsTrans Xle.
Proof. typeclasses eauto. Qed.

End Context.

(** ** Strict Partial Order *)

Fail Fail Class IsStrPartOrd (A : Type) (X : A -> A -> Prop) : Prop := {
  str_part_ord_is_irrefl :> IsIrrefl X;
  str_part_ord_is_trans :> IsTrans X;
}.

Notation IsStrPartOrd := StrictOrder.
Notation str_part_ord_is_irrefl := StrictOrder_Irreflexive.
Notation str_part_ord_is_trans := StrictOrder_Transitive.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** A strict partial order is asymmetric. *)

#[local] Instance str_part_ord_is_asym
  `{!IsStrPartOrd X} : IsAsym X.
Proof. typeclasses eauto. Qed.

(** A strict partial order is a strict preorder. *)

#[export] Instance str_part_ord_is_str_preord
  `{!IsStrPartOrd X} : IsStrPreord X.
Proof. esplit; typeclasses eauto. Qed.

End Context.
