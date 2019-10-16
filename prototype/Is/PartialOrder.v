From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Reflexive Antisymmetric Transitive.

Class IsPartialOrder (A : Type)
  {has_eqv : HasEqv A} {has_ord : HasOrd A} : Prop := {
  partial_order_is_proper :> IsProper (eqv ==> eqv ==> flip impl) ord;
  partial_order_is_reflexive :> IsReflexive ord;
  partial_order_is_antisymmetric :> IsAntisymmetric ord;
  partial_order_is_transitive :> IsTransitive ord;
}.

Add Parametric Morphism {S A : Type}
  `{is_partial_order : IsPartialOrder A} : ord
  with signature eqv ==> eqv ==> flip impl
  as eqv_ord_morphism.
Proof. intros x y p z w q. apply partial_order_is_proper; auto. Qed.

Add Parametric Relation {A : Type}
  `{is_partial_order : IsPartialOrder A} : A ord
  reflexivity proved by partial_order_is_reflexive
  transitivity proved by partial_order_is_transitive
  as partial_order_relation.
