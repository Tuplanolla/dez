(* bad *)
From Coq Require Import
  ZArith.ZArith.
From DEZ.Is Require Export
  Semigroup Monoid Group
  TwoSortedLeftBinaryCommutative.
From DEZ.Provides Require Export
  OneSortedPositiveOperations OneSortedNaturalOperations
  OneSortedIntegerOperations.
From DEZ.Supports Require Import
  OneSortedAdditiveNotations.
From DEZ.Supports Require Import
  OneSortedAdditiveOperationNotations.

Fact succ_xI (n : positive) :
  Pos.succ (xI n) = xO (Pos.succ n).
Proof. reflexivity. Defined.

Fact succ_xO (n : positive) :
  Pos.succ (xO n) = xI n.
Proof. reflexivity. Defined.

Fact succ_xH : Pos.succ xH = xO xH.
Proof. reflexivity. Defined.

Section Context.

Context (A : Type) `{HasBinOp A} `{!IsAssoc eq bin_op}.

Fact iter_op_xI (n : positive) (x : A) :
  Pos.iter_op _+_ (xI n) x = x + Pos.iter_op _+_ n (x + x).
Proof. reflexivity. Defined.

Fact iter_op_xO (n : positive) (x : A) :
  Pos.iter_op _+_ (xO n) x = Pos.iter_op _+_ n (x + x).
Proof. reflexivity. Defined.

Fact iter_op_xH (x : A) :
  Pos.iter_op _+_ xH x = x.
Proof. reflexivity. Defined.

End Context.

Section Context.

Context (A : Type) `{HasBinOp A} `{!IsSemigrp bin_op}.

Lemma iter_op_succ (n : positive) (x : A) :
  Pos.iter_op _+_ (Pos.succ n) x = x + Pos.iter_op _+_ n x.
Proof.
  revert x; induction n as [p IH | p IH |]; intros x.
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

Lemma iter_op_comm (n : positive) (x : A) :
  x + Pos.iter_op _+_ n x = Pos.iter_op _+_ n x + x.
Proof.
  induction n as [| p IH] using Pos.peano_ind.
  - try rewrite (iter_op_xH x).
    reflexivity.
  - rewrite (iter_op_succ p x).
    rewrite IH at 1.
    rewrite (assoc x (Pos.iter_op bin_op p x) x).
    reflexivity. Defined.

End Context.

Section Context.

Context (A : Type) `{IsGrp A}.

Theorem positive_op_un_op_two_l_bin_comm (n : positive) (x : A) :
  - (n * x)%positive = (n * - x)%positive.
Proof.
  cbv [positive_op].
  induction n as [| p IH] using Pos.peano_ind.
  - rewrite (iter_op_xH (- x)).
    rewrite (iter_op_xH x).
    reflexivity.
  - rewrite (iter_op_succ p (- x)).
    rewrite (iter_op_succ p x).
    rewrite (antidistr x (Pos.iter_op bin_op p x)).
    rewrite IH.
    rewrite (iter_op_comm p (- x)).
    reflexivity. Defined.

Global Instance positive_op_un_op_is_two_l_bin_comm :
  IsTwoLBinComm -_ _*_%positive.
Proof. intros x y. apply positive_op_un_op_two_l_bin_comm. Defined.

Theorem n_op_un_op_two_l_bin_comm (n : N) (x : A) :
  - (n * x)%N = (n * - x)%N.
Proof.
  destruct n as [| p].
  - cbv [n_op].
    rewrite fixed.
    reflexivity.
  - cbv [n_op].
    (* Here [rewrite] does not work for some reason. *)
    etransitivity; [| apply (positive_op_un_op_two_l_bin_comm p x)].
    reflexivity. Defined.

Global Instance n_op_un_op_is_two_l_bin_comm : IsTwoLBinComm -_ _*_%N.
Proof. intros x y. apply n_op_un_op_two_l_bin_comm. Defined.

Theorem z_op_un_op_two_l_bin_comm (n : Z) (x : A) :
  - (n * x)%Z = (n * (- x)%grp)%Z.
Proof.
  destruct n as [| p | p].
  - cbv [z_op].
    rewrite fixed.
    reflexivity.
  - cbv [z_op].
    etransitivity; [| apply (positive_op_un_op_two_l_bin_comm p x)].
    reflexivity.
  - cbv [z_op].
    etransitivity; [| apply (f_equal un_op);
      apply (positive_op_un_op_two_l_bin_comm p x)].
    reflexivity. Defined.

Global Instance z_op_un_op_is_two_l_bin_comm : IsTwoLBinComm -_ _*_%Z.
Proof. intros x y. apply z_op_un_op_two_l_bin_comm. Defined.

End Context.
