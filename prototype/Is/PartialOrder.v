From Maniunfold.Has Require Import EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Import Reflexive Antisymmetric Transitive Setoid.

Class IsPartialOrder (A : Type)
  {has_eqv : HasEqv A} {has_ord : HasOrd A} : Prop := {
  ord_proper : ord ::> eqv ==> eqv ==> flip impl;
  ord_is_reflexive :> IsReflexive A;
  ord_is_antisymmetric :> IsAntisymmetric A;
  ord_is_transitive :> IsTransitive A;
}.

Add Parametric Morphism {S A : Type}
  `{is_partial_order : IsPartialOrder A} : ord
  with signature eqv ==> eqv ==> flip impl
  as eqv_ord_morphism.
Proof. intros x y p z w q. apply ord_proper; auto. Qed.

Add Parametric Relation {A : Type}
  `{is_partial_order : IsPartialOrder A} : A ord
  reflexivity proved by ord_is_reflexive
  transitivity proved by ord_is_transitive
  as ord_relation.
