From Maniunfold.Has Require Import Relation EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Import Reflexive Antisymmetric Transitive Connex
  Setoid PartialOrder.

(** TODO This definition causes slow type checking; investigate. *)

Class IsTotalOrder (A : Type)
  {has_eqv : HasEqv A} {has_ord : HasOrd A} : Prop := {
  ord_proper : ord ::> eqv ==> eqv ==> flip impl;
  ord_is_antisymmetric :> IsAntisymmetric A;
  ord_is_transitive :> IsTransitive A;
  ord_is_connex :> IsConnex A;
}.

Add Parametric Morphism {S A : Type} `{is_total_order : IsTotalOrder A} : ord
  with signature eqv ==> eqv ==> flip impl
  as eqv_ord_morphism.
Proof. intros x y p z w q. apply ord_proper; auto. Qed.

Theorem ord_reflexive : forall {A : Type} `{is_total_order : IsTotalOrder A},
  forall x : A, x <= x.
Proof.
  intros A ? ? ? x.
  destruct (ord_is_connex x x) as [p | p].
  - specialize (p : x <= x) as p. apply p.
  - specialize (p : x <= x) as p. apply p. Qed.

Instance ord_is_reflexive {A : Type} `{is_total_order : IsTotalOrder A} :
  IsReflexive A (has_rel := ord) := {}.
Proof. apply ord_reflexive. Qed.

Add Parametric Relation {A : Type} `{is_total_order : IsTotalOrder A} : A ord
  reflexivity proved by ord_is_reflexive
  transitivity proved by ord_is_transitive
  as ord_relation.

Instance total_order_is_partial_order {A : Type}
  `{is_total_order : IsTotalOrder A} : IsPartialOrder A := {}.
Proof. intros x y p z w q. apply ord_proper; auto. Qed.
