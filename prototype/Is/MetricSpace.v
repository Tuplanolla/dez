From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation GroupOperation GroupIdentity Distance.
From Maniunfold.Is Require Export
  TotalOrder CommutativeMonoid.

Import AdditiveNotations.

(** TODO Review literature on "generalized", "monoidal" or
    "semigroup-valued" metric spaces. *)

Class IsMetricSpace (S A : Type)
  {scalar_has_eqv : HasEqv S} {scalar_has_ord : HasOrd S}
  {scalar_has_opr : HasOpr S} {scalar_has_idn : HasIdn S}
  {has_eqv : HasEqv A} {has_dist : HasDist S A} : Prop := {
  scalar_ord_is_total_order :> IsTotalOrder S;
  scalar_opr_is_commutative_monoid :> IsCommutativeMonoid S;
  scalar_opr_left_positive : forall x y : S, y <= x + y;
  scalar_opr_left_monotone : forall x y z : S, x <= y -> z + x <= z + y;
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

Theorem scalar_opr_right_positive : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y : S, x <= x + y.
Proof.
  intros S A ? ? ? ? ? ? ? x y.
  assert (ord ::> eqv ==> eqv ==> flip impl)
    by (apply ord_proper; reflexivity).
  rewrite (opr_commutative x y). apply scalar_opr_left_positive. Qed.

Theorem scalar_opr_right_monotone : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y z : S, x <= y -> x + z <= y + z.
Proof.
  intros S A ? ? ? ? ? ? ? x y z p.
  assert (ord ::> eqv ==> eqv ==> flip impl)
    by (apply ord_proper; reflexivity).
  rewrite (opr_commutative x z). rewrite (opr_commutative y z).
  apply scalar_opr_left_monotone. apply p. Qed.

Theorem scalar_opr_monotone : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x y z w : S, x <= y -> z <= w -> x + z <= y + w.
Proof.
  intros S A ? ? ? ? ? ? ? x y z w p q. transitivity (y + z).
  - apply scalar_opr_right_monotone. apply p.
  - apply scalar_opr_left_monotone. apply q. Qed.

Theorem scalar_nonnegative : forall {S A : Type}
  `{is_metric_space : IsMetricSpace S A},
  forall x : S, 0 <= x.
Proof.
  intros S A ? ? ? ? ? ? ? x.
  assert (ord ::> eqv ==> eqv ==> flip impl)
    by (apply ord_proper; reflexivity).
  rewrite <- (opr_right_identifiable x). apply scalar_opr_left_positive. Qed.
