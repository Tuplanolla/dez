(* bad *)
From Coq Require Import
  ZArith.
From Maniunfold.Is Require Export
  Magma Semigroup Monoid Group TwoSorted.LeftBinaryCommutative.
From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.
From Maniunfold.ShouldOffer Require Import
  OneSorted.AdditiveOperationNotations.

Fact succ_xI : forall n : positive,
  Pos.succ (xI n) = xO (Pos.succ n).
Proof. intros n. reflexivity. Defined.

Fact succ_xO : forall n : positive,
  Pos.succ (xO n) = xI n.
Proof. intros n. reflexivity. Defined.

Fact succ_xH : Pos.succ xH = xO xH.
Proof. reflexivity. Defined.

Section Context.

Context {A : Type} `{is_mag : IsMag A}.

Fact iter_op_xI : forall (n : positive) (x : A),
  Pos.iter_op bin_op (xI n) x = x + Pos.iter_op bin_op n (x + x).
Proof. intros n x. reflexivity. Defined.

Fact iter_op_xO : forall (n : positive) (x : A),
  Pos.iter_op bin_op (xO n) x = Pos.iter_op bin_op n (x + x).
Proof. intros n x. reflexivity. Defined.

Fact iter_op_xH : forall x : A,
  Pos.iter_op bin_op xH x = x.
Proof. intros x. reflexivity. Defined.

End Context.

Section Context.

Context {A : Type} `{is_sgrp : IsSgrp A}.

Lemma iter_op_succ : forall (n : positive) (x : A),
  Pos.iter_op bin_op (Pos.succ n) x = x + Pos.iter_op bin_op n x.
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
    try rewrite (iter_op_xH x).
    reflexivity. Defined.

Lemma iter_op_comm : forall (n : positive) (x : A),
  x + Pos.iter_op bin_op n x = Pos.iter_op bin_op n x + x.
Proof.
  intros n x.
  induction n as [| p IH] using Pos.peano_ind.
  - try rewrite (iter_op_xH x).
    reflexivity.
  - rewrite (iter_op_succ p x).
    rewrite IH at 1.
    rewrite (assoc x (Pos.iter_op bin_op p x) x).
    reflexivity. Defined.

End Context.

Section Context.

Context {A : Type} `{is_grp : IsGrp A}.

Theorem positive_op_un_op_two_l_bin_comm : forall (n : positive) (x : A),
  - (n * x)%positive = (n * - x)%positive.
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
    reflexivity. Defined.

Global Instance positive_op_un_op_is_two_l_bin_comm :
  IsTwoLBinComm positive A un_op positive_op.
Proof. intros x y. apply positive_op_un_op_two_l_bin_comm. Defined.

Theorem n_op_un_op_two_l_bin_comm : forall (n : N) (x : A),
  - (n * x)%N = (n * - x)%N.
Proof.
  intros n x.
  destruct n as [| p].
  - cbv [n_op].
    rewrite un_absorb.
    reflexivity.
  - cbv [n_op].
    rewrite (positive_op_un_op_two_l_bin_comm p x).
    reflexivity. Defined.

Global Instance n_op_un_op_is_two_l_bin_comm : IsTwoLBinComm N A un_op n_op.
Proof. intros x y. apply n_op_un_op_two_l_bin_comm. Defined.

Theorem z_op_un_op_two_l_bin_comm : forall (n : Z) (x : A),
  - (n * x)%Z = (n * (- x)%grp)%Z.
Proof.
  intros n x.
  destruct n as [| p | p].
  - cbv [z_op].
    rewrite un_absorb.
    reflexivity.
  - cbv [z_op].
    rewrite (positive_op_un_op_two_l_bin_comm p x).
    reflexivity.
  - cbv [z_op].
    rewrite (positive_op_un_op_two_l_bin_comm p x).
    reflexivity. Defined.

Global Instance z_op_un_op_is_two_l_bin_comm : IsTwoLBinComm Z A un_op z_op.
Proof. intros x y. apply z_op_un_op_two_l_bin_comm. Defined.

End Context.
