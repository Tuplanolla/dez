From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Antisymmetric Transitive Connex.
From Maniunfold.Is Require Import
  PartialOrder.

Class IsTotalOrder {A : Type} {has_eqv : HasEqv A}
  (has_ord : HasOrd A) : Prop := {
  total_order_ord_is_proper :> IsProper (eqv ==> eqv ==> flip impl) ord;
  total_order_ord_is_antisymmetric :> IsAntisymmetric ord;
  total_order_ord_is_transitive :> IsTransitive ord;
  total_order_ord_is_connex :> IsConnex ord;
}.

Add Parametric Morphism {S A : Type} `{is_total_order : IsTotalOrder A} : ord
  with signature eqv ==> eqv ==> flip impl
  as total_order_ord_morphism.
Proof. apply total_order_ord_is_proper; auto. Qed.

Section Context.

Context {A : Type} `{is_total_order : IsTotalOrder A}.

Theorem total_order_ord_reflexive : forall x : A, x <= x.
Proof.
  intros x. destruct (connex x x) as [H | H].
  - specialize (H : x <= x). apply H.
  - specialize (H : x <= x). apply H. Qed.

Global Instance total_order_ord_is_reflexive : IsReflexive ord := {}.
Proof. apply total_order_ord_reflexive. Qed.

Global Instance total_order_is_partial_order : IsPartialOrder ord := {}.

End Context.

Add Parametric Relation {A : Type} `{is_total_order : IsTotalOrder A} : A ord
  reflexivity proved by total_order_ord_is_reflexive
  transitivity proved by total_order_ord_is_transitive
  as total_order_ord_relation.
