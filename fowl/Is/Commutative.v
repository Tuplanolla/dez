(* * Commutativity *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From DEZ.Has Require Export
  Forms Operations.
From DEZ.Supports Require Import
  MultiplicativeNotations.

Class IsWhatCommL (Z A V Z' A' W : Type) (X : W -> A' -> Prop)
  (f : Z -> A) (g : Z' -> A') (k : A -> V -> W) (m : Z -> V -> Z') : Prop :=
  what_comm_l (x : Z) (y : V) : X (k (f x) y) (g (m x y)).

Class IsWhatCommR (W Y Z' A B B' : Type) (X : W -> Y -> Prop)
  (f : B' -> B) (g : Z' -> Y) (k : A -> B -> W) (m : A -> B' -> Z') : Prop :=
  what_comm_r (x : A) (y : B') : X (k x (f y)) (g (m x y)).

Class IsComm4 (A0 A1 B0 B1 : Type) (X : B0 -> B1 -> Prop)
  (k : A0 -> A1 -> B0) (m : A1 -> A0 -> B1) : Prop :=
  what_comm (x : A0) (y : A1) : X (k x y) (m y x).

(* ** Commutativity of a Unary Operation and a Left Action *)

(** This has the same shape as [mul_opp_r]. *)

Class IsCommL (A B : Type) (X : B -> B -> Prop)
  (f : B -> B) (k : A -> B -> B) : Prop :=
  comm_l (x : A) (y : B) : X (k x (f y)) (f (k x y)).

(* ** Commutativity of a Unary Operation and a Right Action *)

(** This has the same shape as [mul_opp_l]. *)

Class IsCommR (A B : Type) (X : B -> B -> Prop)
  (f : B -> B) (k : B -> A -> B) : Prop :=
  comm_r (x : B) (y : A) : X (k (f x) y) (f (k x y)).

(* ** Commutativity of a Unary Operation and Actions *)

Class IsCommLR2 (A B : Type) (X : B -> B -> Prop)
  (f : B -> B) (k : A -> B -> B) (m : B -> A -> B) : Prop := {
  is_comm_l :> IsCommL X f k;
  is_comm_r :> IsCommR X f m;
}.

(* ** Commutativity of a Unary Operation and a Binary Operation *)

Class IsCommLR (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  is_comm_l_r_2 :> IsCommLR2 X f k k.

(** This has the same shape as [mul_comm]. *)

Class IsComm (A B : Type) (X : B -> B -> Prop) (k : A -> A -> B) : Prop :=
  comm (x y : A) : X (k x y) (k y x).

Class IsCommFun (A : Type) (X : A -> A -> Prop) (f g : A -> A) : Prop :=
  comm_fun (x : A) : X (f (g x)) (g (f x)).

Section Context.

Context (A : Type) `(!@IsComm (A -> A) (A -> A) _=_ _o_).

#[local] Instance is_comm (f g : A -> A) : IsCommFun _=_ f g.
Proof.
  intros x.
  enough ((f o g) x = (g o f) x) by assumption.
  pose proof (comm f g) as a.
  rewrite a.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_comm : typeclass_instances.

Section Context.

Context (A : Type) (x : A) (f : A -> A) (k : A -> A -> A).

(** Chiral commutativity is just commutativity of partial applications. *)

#[local] Instance comm_l_is_comm `(!IsCommL _=_ f k) : IsCommFun _=_ f (k x).
Proof.
  intros y.
  pose proof comm_l (X := _=_) x y as a.
  rewrite a.
  reflexivity. Qed.

#[local] Instance comm_r_is_comm `(!IsCommR _=_ f k) :
  IsCommFun _=_ f (flip k x).
Proof.
  intros y.
  unfold flip.
  pose proof comm_r (X := _=_) y x as a.
  rewrite a.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve comm_l_is_comm comm_r_is_comm : typeclass_instances.
