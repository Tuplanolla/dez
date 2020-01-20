From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  Proper Monoid Invertible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsGrp {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  inv_is_proper :> IsProper (eq_rel ==> eq_rel) un_op;
  opr_idn_is_monoid :> IsMon bin_op un;
  opr_idn_inv_is_invertible :> IsInv bin_op un un_op;
}.

Section Context.

Context {A : Type} `{is_group : IsGrp A}.

Theorem inv_absorbing : - 0 == 0.
Proof.
  rewrite <- (right_unital (- 0)).
  rewrite (left_invertible 0).
  reflexivity. Qed.

Theorem opr_left_injective : forall x y z : A,
  z + x == z + y -> x == y.
Proof.
  intros x y z p.
  rewrite <- (left_unital x).
  rewrite <- (left_invertible z).
  rewrite <- (associative (- z) z x).
  rewrite p.
  rewrite (associative (- z) z y).
  rewrite (left_invertible z).
  rewrite (left_unital y).
  reflexivity. Qed.

Theorem opr_right_injective : forall x y z : A,
  x + z == y + z -> x == y.
Proof.
  intros x y z p.
  rewrite <- (right_unital x).
  rewrite <- (right_invertible z).
  rewrite (associative x z (- z)).
  rewrite p.
  rewrite <- (associative y z (- z)).
  rewrite (right_invertible z).
  rewrite (right_unital y).
  reflexivity. Qed.

Theorem inv_involutive : forall x : A,
  - (- x) == x.
Proof.
  intros x.
  rewrite <- (right_unital (- (- x))).
  rewrite <- (left_invertible x).
  rewrite (associative (- (- x)) (- x) x).
  rewrite (left_invertible (- x)).
  rewrite (left_unital x).
  reflexivity. Qed.

Theorem opr_inv_antidistributive : forall x y : A,
  - (x + y) == (- y) + (- x).
Proof.
  intros x y.
  apply (opr_left_injective (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (right_invertible (x + y)).
  rewrite (associative (x + y) (- y) (- x)).
  rewrite <- (associative x y (- y)).
  rewrite (right_invertible y).
  rewrite (right_unital x).
  rewrite (right_invertible x).
  reflexivity. Qed.

End Context.
