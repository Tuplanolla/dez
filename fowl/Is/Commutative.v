(* * Commutativity *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From DEZ.Has Require Export
  UnaryOperation BinaryOperation Torsion.
From DEZ.ShouldHave Require Import
  MultiplicativeNotations.

Class IsWhatCommL (Z A V Z' A' X : Type) (R : X -> A' -> Prop)
  (f : Z -> A) (g : Z' -> A') (k : A -> V -> X) (m : Z -> V -> Z') : Prop :=
  what_comm_l (x : Z) (y : V) : R (k (f x) y) (g (m x y)).

Class IsWhatCommR (X Y Z' A B B' : Type) (R : X -> Y -> Prop)
  (f : B' -> B) (g : Z' -> Y) (k : A -> B -> X) (m : A -> B' -> Z') : Prop :=
  what_comm_r (x : A) (y : B') : R (k x (f y)) (g (m x y)).

(* ** Commutativity of a Unary Operation and a Left Action *)

(** This has the same shape as [mul_opp_r]. *)

Class IsCommL (A B : Type) (R : B -> B -> Prop)
  (f : B -> B) (k : A -> B -> B) : Prop :=
  comm_l (x : A) (y : B) : R (k x (f y)) (f (k x y)).

(* ** Commutativity of a Unary Operation and a Right Action *)

(** This has the same shape as [mul_opp_l]. *)

Class IsCommR (A B : Type) (R : B -> B -> Prop)
  (f : B -> B) (k : B -> A -> B) : Prop :=
  comm_r (x : B) (y : A) : R (k (f x) y) (f (k x y)).

(* ** Commutativity of a Unary Operation and Actions *)

Class IsCommLR2 (A B : Type) (R : B -> B -> Prop)
  (f : B -> B) (k : A -> B -> B) (m : B -> A -> B) : Prop := {
  is_comm_l :> IsCommL R f k;
  is_comm_r :> IsCommR R f m;
}.

(* ** Commutativity of a Unary Operation and a Binary Operation *)

Class IsCommLR (A : Type) (R : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  is_comm_l_r_2 :> IsCommLR2 R f k k.

(** This has the same shape as [mul_comm]. *)

Class IsCommBinOp (A B : Type) (R : B -> B -> Prop) (k : A -> A -> B) : Prop :=
  comm_bin_op (x y : A) : R (k x y) (k y x).

Class IsComm (A : Type) (R : A -> A -> Prop) (f g : A -> A) : Prop :=
  comm (x : A) : R (f (g x)) (g (f x)).

Section Context.

Context (A : Type) (x : A).

(** Chiral commutativity is just commutativity of partial applications. *)

#[local] Instance comm_r_is_comm `(!IsCommL R f k) : IsComm R f (k x).
Proof.
  intros y.
  rewrite comm_r.
  reflexivity. Qed.

#[local] Instance comm_l_is_comm `(!IsCommR R f k) : IsComm R f (flip f x).
Proof.
  intros y.
  unfold flip.
  rewrite comm_l.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve comm_l_is_comm comm_r_is_comm : typeclass_instances.
