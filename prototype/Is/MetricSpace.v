From Maniunfold.Has Require Import EquivalenceRelation OrderRelation Distance
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Import Associative Identifiable Invertible
  Setoid TotalOrder CommutativeMonoid.

Import AdditiveNotations.

Class IsMetricSpace (S A : Type)
  {scalar_has_eqv : HasEqv S} {scalar_has_ord : HasOrd S}
  {scalar_has_opr : HasOpr S} {scalar_has_idn : HasIdn S}
  {has_eqv : HasEqv A} {has_dist : HasDist S A} : Prop := {
  scalar_ord_is_total_order :> IsTotalOrder S;
  scalar_opr_is_commutative_monoid :> IsCommutativeMonoid S;
  dist_proper : dist ::> eqv ==> eqv ==> eqv;
  dist_indiscernible : forall x y : A, dist x y == 0 <-> x == y;
  dist_symmetric : forall x y : A, dist x y == dist y x;
  dist_triangle : forall x y z : A, dist x z <= dist x y + dist y z;
}.

Add Parametric Morphism {S A : Type}
  `{is_metric_space : IsMetricSpace S A} : dist
  with signature eqv ==> eqv ==> eqv
  as eqv_dist_morphism.
Proof. intros x y p z w q. apply dist_proper; auto. Qed.
