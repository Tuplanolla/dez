From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  Proper Monoid Invertible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsGrp {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  un_op_is_proper :> IsProper (eq_rel ==> eq_rel) un_op;
  bin_op_un_is_mon :> IsMon bin_op un;
  bin_op_un_un_op_is_inv :> IsInv bin_op un un_op;
}.

Section Context.

Context {A : Type} `{is_grp : IsGrp A}.

Theorem un_op_absorb : - 0 == 0.
Proof.
  rewrite <- (r_un (- 0)).
  rewrite (l_inv 0).
  reflexivity. Qed.

Theorem bin_op_l_inj : forall x y z : A,
  z + x == z + y -> x == y.
Proof.
  intros x y z p.
  rewrite <- (l_un x).
  rewrite <- (l_inv z).
  rewrite <- (assoc (- z) z x).
  rewrite p.
  rewrite (assoc (- z) z y).
  rewrite (l_inv z).
  rewrite (l_un y).
  reflexivity. Qed.

Theorem bin_op_r_inj : forall x y z : A,
  x + z == y + z -> x == y.
Proof.
  intros x y z p.
  rewrite <- (r_un x).
  rewrite <- (r_inv z).
  rewrite (assoc x z (- z)).
  rewrite p.
  rewrite <- (assoc y z (- z)).
  rewrite (r_inv z).
  rewrite (r_un y).
  reflexivity. Qed.

Theorem un_op_invol : forall x : A,
  - (- x) == x.
Proof.
  intros x.
  rewrite <- (r_un (- (- x))).
  rewrite <- (l_inv x).
  rewrite (assoc (- (- x)) (- x) x).
  rewrite (l_inv (- x)).
  rewrite (l_un x).
  reflexivity. Qed.

Theorem bin_op_un_op_antidistr : forall x y : A,
  - (x + y) == (- y) + (- x).
Proof.
  intros x y.
  apply (bin_op_l_inj (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (r_inv (x + y)).
  rewrite (assoc (x + y) (- y) (- x)).
  rewrite <- (assoc x y (- y)).
  rewrite (r_inv y).
  rewrite (r_un x).
  rewrite (r_inv x).
  reflexivity. Qed.

End Context.
