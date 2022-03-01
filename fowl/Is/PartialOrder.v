(** * Partial Ordering *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations.
From DEZ.Is Require Export
  Equivalence Preorder Antisymmetric Proper.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations.

#[local] Existing Instance antisymmetric_is_antisym.

(** ** Partial Order *)
(** ** Poset *)

(** We cannot define [IsPartOrd] as a notation for [PartialOrder],
    because [PartialOrder] is constrained by [Equivalence] and [PreOrder] and
    built from [relation_equivalence]. *)

Fail Fail Notation IsPartOrd := PartialOrder.

Class IsPartOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  part_ord_is_equiv :> IsEquiv X;
  part_ord_is_preord :> IsPreord Y;
  part_ord_is_antisym :> IsAntisym X Y;
  part_ord_is_proper :> IsProper (X ==> X ==> _<->_) Y;
}.

Section Context.

Context (A : Type) (X Y : A -> A -> Prop) `{!IsEquiv X} `{!IsPreord Y}.

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_ord_rel : HasOrdRel A := Y.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change Y with (ord_rel (A := A)) in *).

(** Standard library partial order implies our partial order. *)

#[local] Instance partial_order_is_part_ord
  `{!PartialOrder X Y} : IsPartOrd X Y.
Proof. esplit; typeclasses eauto. Qed.

(** Our partial order implies standard library partial order. *)

#[local] Instance part_ord_partial_order
  `{!IsPartOrd X Y} : PartialOrder X Y.
Proof.
  note. intros x y. unfold pointwise_lifting, relation_conjunction.
  unfold predicate_intersection. unfold pointwise_extension. unfold flip.
  pose proof antisym x y as a.
  pose proof fun a : x == y => part_ord_is_proper x x id x y a as b.
  pose proof fun a : x == y => part_ord_is_proper y y id y x (a ^-1) as c.
  intuition. Qed.

End Context.
