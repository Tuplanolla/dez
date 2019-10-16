From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation GroupOperation GroupIdentity Distance.
From Maniunfold.Is Require Export
  TotalOrder CommutativeMonoid.

Import AdditiveNotations.

(** TODO Review literature on "generalized", "monoidal" or
    "semigroup-valued" metric spaces. *)

Class IsMetricSpace (S A : Type)
  {S_has_eqv : HasEqv S} {S_has_ord : HasOrd S}
  {S_has_opr : HasOpr S} {S_has_idn : HasIdn S}
  {A_has_eqv : HasEqv A} {has_dist : HasDist S A} : Prop := {
  S_ord_is_total_order :> IsTotalOrder S;
  S_opr_is_commutative_monoid :> IsCommutativeMonoid S;
  S_opr_left_positive : forall x y : S, y <= x + y;
  S_opr_left_monotone : forall x y z : S, x <= y -> z + x <= z + y;
  dist_proper :> IsProper (eqv ==> eqv ==> eqv) dist;
  dist_indiscernible : forall x y : A, dist x y == 0 <-> x == y;
  dist_symmetric : forall x y : A, dist x y == dist y x;
  dist_triangle : forall x y z : A, dist x z <= dist x y + dist y z;
}.

Add Parametric Morphism {S A : Type}
  `{is_metric_space : IsMetricSpace S A} : dist
  with signature eqv ==> eqv ==> eqv
  as eqv_dist_morphism.
Proof. intros x y p z w q. apply dist_proper; auto. Qed.

Theorem S_opr_right_positive : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y : S, x <= x + y.
Proof.
  intros S A ? ? ? ? ? ? ? x y.
  rewrite (opr_commutative x y). apply S_opr_left_positive. Qed.

Theorem S_opr_right_monotone : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y z : S, x <= y -> x + z <= y + z.
Proof.
  intros S A ? ? ? ? ? ? ? x y z p.
  rewrite (opr_commutative x z). rewrite (opr_commutative y z).
  apply S_opr_left_monotone. apply p. Qed.

Theorem S_opr_monotone : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y z w : S, x <= y -> z <= w -> x + z <= y + w.
Proof.
  intros S A ? ? ? ? ? ? ? x y z w p q. transitivity (y + z).
  - apply S_opr_right_monotone. apply p.
  - apply S_opr_left_monotone. apply q. Qed.

Theorem S_ord_nonnegative : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x : S, 0 <= x.
Proof.
  intros S A ? ? ? ? ? ? ? x.
  rewrite <- (opr_right_identifiable x). apply S_opr_left_positive. Qed.
