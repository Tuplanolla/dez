From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  Monoid Invertible Involutive Antidistributive.

Import AdditiveNotations.

Class IsGroup {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) (has_inv : HasInv A) : Prop := {
  group_inv_is_proper :> IsProper (eqv ==> eqv) inv;
  group_is_monoid :> IsMonoid opr idn;
  group_is_invertible :> IsInvertible opr idn inv;
}.

Section Context.

Context {A : Type} `{is_group : IsGroup A}.

Global Add Parametric Morphism : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof. apply group_inv_is_proper; auto. Qed.

Lemma idn_inv : - 0 == 0.
Proof.
  rewrite <- (right_identifiable (- 0)).
  rewrite (left_invertible 0).
  reflexivity. Qed.

Lemma left_injective : forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros x y z p.
  rewrite <- (left_identifiable x).
  rewrite <- (left_invertible z).
  rewrite <- (associative (- z) z x).
  rewrite p.
  rewrite (associative (- z) z y).
  rewrite (left_invertible z).
  rewrite (left_identifiable y).
  reflexivity. Qed.

Lemma right_injective : forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros x y z p.
  rewrite <- (right_identifiable x).
  rewrite <- (right_invertible z).
  rewrite (associative x z (- z)).
  rewrite p.
  rewrite <- (associative y z (- z)).
  rewrite (right_invertible z).
  rewrite (right_identifiable y).
  reflexivity. Qed.

Theorem inv_involutive : forall x : A, - (- x) == x.
Proof.
  intros x.
  rewrite <- (right_identifiable (- (- x))).
  rewrite <- (left_invertible x).
  rewrite (associative (- (- x)) (- x) x).
  rewrite (left_invertible (- x)).
  rewrite (left_identifiable x).
  reflexivity. Qed.

Global Instance : IsInvolutive inv := {}.
Proof. apply inv_involutive. Qed.

Theorem inv_antidistributive : forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros x y.
  apply (left_injective (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (right_invertible (x + y)).
  rewrite (associative (x + y) (- y) (- x)).
  rewrite <- (associative x y (- y)).
  rewrite (right_invertible y).
  rewrite (right_identifiable x).
  rewrite (right_invertible x).
  reflexivity. Qed.

Global Instance : IsAntidistributive opr inv := {}.
Proof. apply inv_antidistributive. Qed.

End Context.
