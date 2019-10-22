From Coq Require Import
  ZArith.
From Maniunfold Require Export
  Init.
From Maniunfold.Is Require Import
  Group.
From Maniunfold.Provides Require Import
  PositivePowers NaturalPowers IntegerPowers.
From Maniunfold.Supports Require Import
  OrderNotations AdditiveGroupNotations.

Section Context.

Context {A : Type} `{is_setoid : IsSetoid A}.

(** We need a setoid version of the standard library lemma [iter_op_succ]. *)

Lemma iter_op_succ : forall (op : A -> A -> A),
  (forall x y z : A, op x (op y z) == op (op x y) z) ->
  forall (n : positive) (x : A),
  Pos.iter_op op (Pos.succ n) x == op x (Pos.iter_op op n x).
Proof.
  intros op p n. induction n as [q r | q r |]; intros x.
  - rewrite (p x x (Pos.iter_op op q (op x x))). rewrite (r (op x x)). reflexivity.
  - reflexivity.
  - reflexivity. Qed.

Corollary iter_op_comm : forall (op : A -> A -> A),
  (IsProper (eqv ==> eqv ==> eqv) op) ->
  (forall x y z : A, op x (op y z) == op (op x y) z) ->
  forall (n : positive) (x : A),
  op x (Pos.iter_op op n x) == op (Pos.iter_op op n x) x.
Proof.
  intros op p q n x. induction n as [| r s] using Pos.peano_ind.
  - reflexivity.
  - rewrite (iter_op_succ op q r x). rewrite s.
    rewrite (q x (Pos.iter_op op r x) x). rewrite <- s. reflexivity. Qed.

End Context.

Section Context.

Context {A : Type} `{is_group : IsGroup A}.

Theorem popr_inv_distributive : forall (n : positive) (x : A),
  (n * (- x))%positive == - (n * x)%positive.
Proof.
  intros n x. cbv [popr]. induction n as [| p q] using Pos.peano_ind.
  - reflexivity.
  - rewrite (iter_op_succ opr associative p (- x)),
      (iter_op_succ opr associative p x).
    rewrite q. rewrite <- (antidistributive (Pos.iter_op opr p x) x).
    rewrite (iter_op_comm opr proper associative p x).
    reflexivity. Qed.

Theorem nopr_inv_distributive : forall (n : N) (x : A),
  (n * (- x))%N == - (n * x)%N.
Proof.
  intros n x.
  destruct n as [| p].
  - cbv [nopr]. rewrite inv_absorbing. reflexivity.
  - cbv [nopr]. apply (popr_inv_distributive p x). Qed.

Theorem zopr_inv_distributive : forall (n : Z) (x : A),
  (n * (- x)%group)%Z == - (n * x)%Z.
Proof.
  intros n x.
  destruct n as [| p | p].
  - cbv [zopr]. rewrite inv_absorbing. reflexivity.
  - cbv [zopr]. apply (popr_inv_distributive p x).
  - cbv [zopr]. rewrite (involutive (p * x)%positive).
    rewrite (popr_inv_distributive p x).
    rewrite (involutive (p * x)%positive). reflexivity. Qed.

End Context.
