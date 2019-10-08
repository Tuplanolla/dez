From Coq Require Import ZArith.
From Maniunfold.Has Require Import EquivalenceRelation
  Operation Identity Inverse.
From Maniunfold.Is Require Import Associative LeftIdentity RightIdentity
  LeftInverse RightInverse Setoid Semigroup Monoid Group.
From Maniunfold.Shall Require Import IntegerPower.

Import AdditiveNotations Pos.

Theorem inv_involutive : forall {A : Type} `{is_group : IsGroup A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? grp x.
  rewrite <- (opr_right_identity (- (- x))). rewrite <- (opr_left_inverse x).
  rewrite (opr_associative (- (- x)) (- x) x).
  rewrite (opr_left_inverse (- x)). rewrite (opr_left_identity x).
  reflexivity. Qed.

Lemma opr_left_injective : forall {A : Type} `{is_group : IsGroup A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A ? ? ? ? grp x y z p.
  rewrite <- (opr_left_identity x). rewrite <- (opr_left_inverse z).
  rewrite <- (opr_associative (- z) z x). rewrite p.
  rewrite (opr_associative (- z) z y). rewrite (opr_left_inverse z).
  rewrite (opr_left_identity y). reflexivity. Qed.

Lemma opr_right_injective : forall {A : Type} `{is_group : IsGroup A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A ? ? ? ? grp x y z p.
  rewrite <- (opr_right_identity x). rewrite <- (opr_right_inverse z).
  rewrite (opr_associative x z (- z)). rewrite p.
  rewrite <- (opr_associative y z (- z)). rewrite (opr_right_inverse z).
  rewrite (opr_right_identity y). reflexivity. Qed.

Theorem opr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? grp x y.
  apply (opr_left_injective (- (x + y)) ((- y) + (- x)) (x + y)).
  rewrite (opr_right_inverse (x + y)).
  rewrite (opr_associative (x + y) (- y) (- x)).
  rewrite <- (opr_associative x y (- y)). rewrite (opr_right_inverse y).
  rewrite (opr_right_identity x). rewrite (opr_right_inverse x).
  reflexivity. Qed.

Theorem idn_inv_absorbing : forall {A : Type} `{is_group : IsGroup A},
  - 0 == 0.
Proof.
  intros A ? ? ? ? grp.
  rewrite <- (opr_right_identity (- 0)). rewrite (opr_left_inverse 0).
  reflexivity. Qed.

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
  (op : A -> A -> A), (op ::> eqv ==> eqv ==> eqv) ->
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
  (n *^ (- x) == - (n *^ x))%positive.
Proof.
  intros A ? ? ? ? grp n x. cbv [popr]. induction n as [| p q] using peano_ind.
  - reflexivity.
  - rewrite (iter_op_succ opr opr_associative p (- x)),
      (iter_op_succ opr opr_associative p x).
    rewrite q. rewrite <- (opr_inv_distributive (iter_op opr p x) x).
    rewrite (iter_op_comm opr opr_proper opr_associative p x).
    reflexivity. Qed.

Theorem nopr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall (n : N) (x : A), (n *^ (- x) == - (n *^ x))%N.
Proof.
  intros A ? ? ? ? grp n x.
  destruct n as [| p].
  - cbv [nopr]. rewrite idn_inv_absorbing. reflexivity.
  - cbv [nopr]. rewrite (popr_inv_distributive p x). reflexivity. Qed.

Theorem zopr_inv_distributive : forall {A : Type} `{is_group : IsGroup A},
  forall (n : Z) (x : A), (n *^ (- x)%inverse)%Z == - (n *^ x)%Z.
Proof.
  intros A ? ? ? ? grp n x.
  destruct n as [| p | p].
  - cbv [zopr]. rewrite idn_inv_absorbing. reflexivity.
  - cbv [zopr]. rewrite (popr_inv_distributive p x). reflexivity.
  - cbv [zopr]. rewrite (inv_involutive (p *^ x)%positive).
    rewrite (popr_inv_distributive p x).
    rewrite (inv_involutive (p *^ x)%positive). reflexivity. Qed.
