(** * Partial Ordering *)

From DEZ.Has Require Export
  EquivalenceRelation OrderRelations.
From DEZ.Is Require Export
  Equivalence Preorder Antisymmetric Proper.
From DEZ.ShouldHave Require Import
  EquivalenceNotations OrderRelationNotations.

#[local] Open Scope relation_scope.

(** ** Partial Order *)
(** ** Poset *)

(** We cannot define [IsPartOrd] as a notation for [PartialOrder],
    because [PartialOrder] is constrained by [Equivalence] and
    built from [relation_equivalence]. *)

Fail Fail Notation IsPartOrd := PartialOrder.

Class IsPartOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  is_eq :> IsEq X;
  is_preord :> IsPreord Y;
  is_antisym :> IsAntisym X Y;
  is_proper :> IsProper (X ==> X ==> _<->_) Y;
}.

(** Our definition is equivalent to the one in the standard library. *)

Section Context.

Context (A : Type) (X Y : A -> A -> Prop) `{!IsEq X}.

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_ord_rel : HasOrdRel A := Y.

Ltac note := progress (
  try change X with _==_ in *;
  try change Y with _<=_ in *).

#[export] Instance is_part_ord
  `{!IsPreord Y} `{!PartialOrder X Y} : IsPartOrd X Y.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance partial_order
  `{!IsPartOrd X Y} : PartialOrder X Y.
Proof.
  note.
  intros x y.
  unfold pointwise_lifting, relation_conjunction.
  unfold predicate_intersection. unfold pointwise_extension. unfold flip.
  pose proof antisym x y.
  pose proof fun a : x == y => is_proper x x (id x) x y a.
  pose proof fun a : x == y => is_proper y y (id y) y x (a ^-1).
  intuition. Qed.

End Context.
