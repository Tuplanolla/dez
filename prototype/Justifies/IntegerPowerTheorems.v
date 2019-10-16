From Coq Require Import
  ZArith.
From Maniunfold.Is Require Import
  Group.
From Maniunfold.Justifies Require Import
  IntegerPowers.

Import Pos AdditiveNotations.

(** We need a setoid version of the standard library lemma [iter_op_succ]. *)
Lemma iter_op_succ : forall {A : Type} `{is_setoid : IsSetoid A}
  (op : A -> A -> A),
  (forall x y z : A, op x (op y z) == op (op x y) z) ->
  forall (n : positive) (x : A),
  iter_op op (succ n) x == op x (iter_op op n x).
Proof.
  intros A ? ? op p n. induction n as [q r | q r |]; intros x.
  - rewrite (p x x (iter_op op q (op x x))). rewrite (r (op x x)). reflexivity.
  - reflexivity.
  - reflexivity. Qed.

Corollary iter_op_comm : forall {A : Type} `{is_setoid : IsSetoid A}
  (op : A -> A -> A), (IsProper (eqv ==> eqv ==> eqv) op) ->
  (forall x y z : A, op x (op y z) == op (op x y) z) ->
  forall (n : positive) (x : A),
  op x (iter_op op n x) == op (iter_op op n x) x.
Proof.
  intros A ? ? op p q n x. induction n as [| r s] using peano_ind.
  - reflexivity.
  - rewrite (iter_op_succ op q r x). rewrite s.
    rewrite (q x (iter_op op r x) x). rewrite <- s. reflexivity. Qed.

Theorem popr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall (n : positive) (x : A),
  (n * (- x))%positive == - (n * x)%positive.
Proof.
  intros A ? ? ? ? ? n x. cbv [popr]. induction n as [| p q] using peano_ind.
  - reflexivity.
  - rewrite (iter_op_succ opr opr_associative p (- x)),
      (iter_op_succ opr opr_associative p x).
    rewrite q. rewrite <- (inv_opr_antidistributive (iter_op opr p x) x).
    rewrite (iter_op_comm opr opr_proper opr_associative p x).
    reflexivity. Qed.

Theorem nopr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall (n : N) (x : A), (n * (- x))%N == - (n * x)%N.
Proof.
  intros A ? ? ? ? ? n x.
  destruct n as [| p].
  - cbv [nopr]. rewrite idn_inv. reflexivity.
  - cbv [nopr]. rewrite (popr_inv_distributive p x). reflexivity. Qed.

Theorem zopr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall (n : Z) (x : A), (n * (- x)%group)%Z == - (n * x)%Z.
Proof.
  intros A ? ? ? ? ? n x.
  destruct n as [| p | p].
  - cbv [zopr]. rewrite idn_inv. reflexivity.
  - cbv [zopr]. rewrite (popr_inv_distributive p x). reflexivity.
  - cbv [zopr]. rewrite (inv_involutive (p * x)%positive).
    rewrite (popr_inv_distributive p x).
    rewrite (inv_involutive (p * x)%positive). reflexivity. Qed.
