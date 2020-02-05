From Coq Require Import
  ZArith.
From Maniunfold.Is Require Export
  Equivalence Magma Semigroup Monoid Group RightExternallyBinaryCommutative.
From Maniunfold.Offers Require Export
  PositivePowers NaturalPowers IntegerPowers.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.
From Maniunfold.ShouldOffer Require Import
  MoreAdditiveNotations.

Fact succ_xI : forall n : positive,
  Pos.succ (xI n) = xO (Pos.succ n).
Proof. intros n. reflexivity. Qed.

Fact succ_xO : forall n : positive,
  Pos.succ (xO n) = xI n.
Proof. intros n. reflexivity. Qed.

Fact succ_xH : Pos.succ xH = xO xH.
Proof. reflexivity. Qed.

Section Context.

Context {A : Type} `{is_mag : IsMag A}.

Fact iter_op_xI : forall (n : positive) (x : A),
  Pos.iter_op bin_op (xI n) x == x + Pos.iter_op bin_op n (x + x).
Proof. intros n x. reflexivity. Qed.

Fact iter_op_xO : forall (n : positive) (x : A),
  Pos.iter_op bin_op (xO n) x == Pos.iter_op bin_op n (x + x).
Proof. intros n x. reflexivity. Qed.

Fact iter_op_xH : forall x : A,
  Pos.iter_op bin_op xH x == x.
Proof. intros x. reflexivity. Qed.

End Context.

Section Context.

Context {A : Type} `{is_sgrp : IsSgrp A}.

Lemma iter_op_succ : forall (n : positive) (x : A),
  Pos.iter_op bin_op (Pos.succ n) x == x + Pos.iter_op bin_op n x.
Proof.
  intros n.
  induction n as [p IH | p IH |]; intros x.
  - rewrite (succ_xI p).
    rewrite (iter_op_xO (Pos.succ p) x).
    rewrite (IH (bin_op x x)).
    rewrite (iter_op_xI p x).
    rewrite (assoc x x (Pos.iter_op bin_op p (bin_op x x))).
    reflexivity.
  - rewrite (succ_xO p).
    rewrite (iter_op_xI p x).
    rewrite (iter_op_xO p x).
    reflexivity.
  - rewrite succ_xH.
    rewrite (iter_op_xO xH x).
    rewrite (iter_op_xH (x + x)).
    rewrite (iter_op_xH x).
    reflexivity. Qed.

Lemma iter_op_comm : forall (n : positive) (x : A),
  x + Pos.iter_op bin_op n x == Pos.iter_op bin_op n x + x.
Proof.
  intros n x.
  induction n as [| p IH] using Pos.peano_ind.
  - rewrite (iter_op_xH x).
    reflexivity.
  - rewrite (iter_op_succ p x).
    rewrite IH at 1.
    rewrite (assoc x (Pos.iter_op bin_op p x) x).
    reflexivity. Qed.

End Context.

Section Context.

Context {A : Type} `{is_grp : IsGrp A}.

Theorem positive_op_un_op_r_ext_bin_comm : forall (n : positive) (x : A),
  - (n * x)%positive == (n * - x)%positive.
Proof.
  intros n x.
  cbv [positive_op].
  induction n as [| p IH] using Pos.peano_ind.
  - rewrite (iter_op_xH (- x)).
    rewrite (iter_op_xH x).
    reflexivity.
  - rewrite (iter_op_succ p (- x)).
    rewrite (iter_op_succ p x).
    rewrite (un_antidistr x (Pos.iter_op bin_op p x)).
    rewrite IH.
    rewrite (iter_op_comm p (- x)).
    reflexivity. Qed.

Global Instance positive_op_un_op_is_r_ext_bin_comm :
  IsRExtBinComm positive_op un_op.
Proof. intros x y. apply positive_op_un_op_r_ext_bin_comm. Qed.

Theorem n_op_un_op_r_ext_bin_comm : forall (n : N) (x : A),
  - (n * x)%N == (n * - x)%N.
Proof.
  intros n x.
  destruct n as [| p].
  - cbv [n_op].
    rewrite un_absorb.
    reflexivity.
  - cbv [n_op].
    rewrite (positive_op_un_op_r_ext_bin_comm p x).
    reflexivity. Qed.

Global Instance n_op_un_op_is_r_ext_bin_comm : IsRExtBinComm n_op un_op.
Proof. intros x y. apply n_op_un_op_r_ext_bin_comm. Qed.

Theorem z_op_un_op_r_ext_bin_comm : forall (n : Z) (x : A),
  - (n * x)%Z == (n * (- x)%algebra)%Z.
Proof.
  intros n x.
  destruct n as [| p | p].
  - cbv [z_op].
    rewrite un_absorb.
    reflexivity.
  - cbv [z_op].
    rewrite (positive_op_un_op_r_ext_bin_comm p x).
    reflexivity.
  - cbv [z_op].
    rewrite (positive_op_un_op_r_ext_bin_comm p x).
    reflexivity. Qed.

Global Instance z_op_un_op_is_r_ext_bin_comm : IsRExtBinComm z_op un_op.
Proof. intros x y. apply z_op_un_op_r_ext_bin_comm. Qed.

End Context.
