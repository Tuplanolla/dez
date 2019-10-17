From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation GroupOperation GroupIdentity Distance.
From Maniunfold.Is Require Export
  TotalOrder CommutativeMonoid.

Import AdditiveNotations.

(** TODO Review literature on "generalized", "monoidal" or
    "semigroup-valued" metric spaces. *)

Class IsMetricSpace {S A : Type}
  {S_has_eqv : HasEqv S} {S_has_ord : HasOrd S}
  (S_has_opr : HasOpr S) (S_has_idn : HasIdn S)
  {A_has_eqv : HasEqv A} (has_dist : HasDist S A) : Prop := {
  metric_space_S_ord_is_total_order :> IsTotalOrder ord;
  metric_space_S_opr_is_commutative_monoid :> IsCommutativeMonoid opr idn;
  metric_space_S_opr_left_positive : forall x y : S,
    y <= x + y;
  metric_space_S_opr_left_monotone : forall x y z : S,
    x <= y -> z + x <= z + y;
  metric_space_dist_is_proper :> IsProper (eqv ==> eqv ==> eqv) dist;
  metric_space_dist_indiscernible : forall x y : A,
    dist x y == 0 <-> x == y;
  metric_space_dist_symmetric : forall x y : A,
    dist x y == dist y x;
  metric_space_dist_triangle : forall x y z : A,
    dist x z <= dist x y + dist y z;
}.

Add Parametric Morphism {S A : Type}
  `{is_metric_space : IsMetricSpace S A} : dist
  with signature eqv ==> eqv ==> eqv
  as eqv_dist_morphism.
Proof. apply metric_space_dist_is_proper; auto. Qed.

Theorem metric_space_S_opr_right_positive : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y : S, x <= x + y.
Proof.
  intros S A ? ? ? ? ? ? ? x y.
  rewrite (commutative x y). apply metric_space_S_opr_left_positive. Qed.

Theorem metric_space_S_opr_right_monotone : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y z : S, x <= y -> x + z <= y + z.
Proof.
  intros S A ? ? ? ? ? ? ? x y z p.
  rewrite (commutative x z). rewrite (commutative y z).
  apply metric_space_S_opr_left_monotone. apply p. Qed.

Theorem metric_space_S_opr_monotone : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y z w : S, x <= y -> z <= w -> x + z <= y + w.
Proof.
  intros S A ? ? ? ? ? ? ? x y z w p q. transitivity (y + z).
  - apply metric_space_S_opr_right_monotone. apply p.
  - apply metric_space_S_opr_left_monotone. apply q. Qed.

Theorem metric_space_S_ord_nonnegative : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x : S, 0 <= x.
Proof.
  intros S A ? ? ? ? ? ? ? x.
  rewrite <- (right_identifiable x). apply metric_space_S_opr_left_positive. Qed.
