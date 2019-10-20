From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation GroupOperation GroupIdentity Distance.
From Maniunfold.Is Require Export
  Proper TotalOrder CommutativeMonoid Heterocommutative.

Import AdditiveNotations.

(** TODO Review literature on "generalized", "monoidal" or
    "semigroup-valued" metric spaces. *)

Class IsMetricSpace {S A : Type}
  {S_has_eqv : HasEqv S} {S_has_ord : HasOrd S}
  (S_has_opr : HasOpr S) (S_has_idn : HasIdn S)
  {A_has_eqv : HasEqv A} (has_dist : HasDist S A) : Prop := {
  dist_is_proper :> IsProper (eqv ==> eqv ==> eqv) dist;
  ord_is_total_order :> IsTotalOrder ord;
  opr_idn_is_commutative_monoid :> IsCommutativeMonoid opr idn;
  dist_is_heterocommutative :> IsHeterocommutative dist;
  left_positive : forall x y : S, y <= x + y;
  left_monotone : forall x y z : S, x <= y -> z + x <= z + y;
  indiscernible : forall x y : A, dist x y == 0 <-> x == y;
  triangular : forall x y z : A, dist x z <= dist x y + dist y z;
}.

Section Context.

Context {S A : Type} `{is_metric_space : IsMetricSpace S A}.

Theorem right_positive : forall x y : S,
  x <= x + y.
Proof.
  intros x y. rewrite (commutative x y). apply left_positive. Qed.

Theorem right_monotone : forall x y z : S,
  x <= y -> x + z <= y + z.
Proof.
  intros x y z p. rewrite (commutative x z). rewrite (commutative y z).
  apply left_monotone. apply p. Qed.

Theorem monotone : forall x y z w : S,
  x <= y -> z <= w -> x + z <= y + w.
Proof.
  intros x y z w p q. transitivity (y + z).
  - apply right_monotone. apply p.
  - apply left_monotone. apply q. Qed.

Theorem nonnegative : forall x : S,
  0 <= x.
Proof.
  intros x.
  rewrite <- (right_identifiable x). apply left_positive. Qed.

End Context.
