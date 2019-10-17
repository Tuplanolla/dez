From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Antisymmetric Transitive Connex.
From Maniunfold.Is Require Import
  PartialOrder.

(** TODO This definition causes slow type checking; investigate. *)

Class IsTotalOrder {A : Type} {has_eqv : HasEqv A}
  (has_ord : HasOrd A) : Prop := {
  total_order_is_proper :> IsProper (eqv ==> eqv ==> flip impl) ord;
  total_order_is_antisymmetric :> IsAntisymmetric ord;
  total_order_is_transitive :> IsTransitive ord;
  total_order_is_connex :> IsConnex ord;
}.

Add Parametric Morphism {S A : Type} `{is_total_order : IsTotalOrder A} : ord
  with signature eqv ==> eqv ==> flip impl
  as eqv_ord_morphism.
Proof. apply total_order_is_proper; auto. Qed.

Theorem total_order_reflexive : forall {A : Type}
  `{is_total_order : IsTotalOrder A},
  forall x : A, x <= x.
Proof.
  intros A ? ? ? x.
  destruct (connex x x) as [p | p].
  - specialize (p : x <= x) as p. apply p.
  - specialize (p : x <= x) as p. apply p. Qed.

Instance total_order_is_reflexive {A : Type}
  `{is_total_order : IsTotalOrder A} : IsReflexive ord := {}.
Proof. apply total_order_reflexive. Qed.

Add Parametric Relation {A : Type} `{is_total_order : IsTotalOrder A} : A ord
  reflexivity proved by total_order_is_reflexive
  transitivity proved by total_order_is_transitive
  as total_order_relation.

Instance total_order_is_partial_order {A : Type}
  `{is_total_order : IsTotalOrder A} : IsPartialOrder A := {}.
