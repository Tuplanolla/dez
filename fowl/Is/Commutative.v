(* * Commutativity *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From DEZ.Has Require Export
  Forms Operations.

(** ** Left-Commutative Unary Functions over Binary Functions *)

Class IsCommBinOpL (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (f : A0 -> B0) (k : A0 -> A1 -> B1)
  (g : B1 -> C) (m : B0 -> A1 -> C) : Prop :=
  comm_bin_op_l (x : A0) (y : A1) : X (m (f x) y) (g (k x y)).

(** ** Right-Commutative Unary Functions over Binary Functions *)

Class IsCommBinOpR (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (f : A1 -> B1) (k : A0 -> A1 -> B1)
  (g : B1 -> C) (m : A0 -> B1 -> C) : Prop :=
  comm_bin_op_r (x : A0) (y : A1) : X (m x (f y)) (g (k x y)).

Compute @IsCommBinOpL ?[A0] ?[A1] ?[B0] ?[B1] ?[C].

(** Is there a symmetry? *)

Compute @IsCommBinOpL ?[A] ?[C] ?[B] ?C ?C. (* LL does not unify *)
Compute @IsCommBinOpL ?[B] ?[A] ?[C] ?B ?C. (* RR unifies f g *)
Compute @IsCommBinOpL ?[A] ?[B] ?[C] ?B ?C. (* LR does not unify *)
Compute @IsCommBinOpL ?[C] ?[B] ?[A] ?C ?B. (* RL does not unify *)
Compute @IsCommBinOpL ?[C] ?C ?C ?[A] ?[B]. (* FF does not unify *)

(** How about skew symmetry? *)

Compute @IsCommBinOpL ?[C] ?C ?[A] ?[B] ?C. (* FL does not unify but is nice *)
Compute @IsCommBinOpL ?[B] ?B ?[C] ?[A] ?C. (* FR does not unify but is nice *)
Compute @IsCommBinOpL ?[B] ?B ?[A] ?B ?B. (* BL does not unify *)
Compute @IsCommBinOpL ?[A] ?A ?[B] ?A ?B. (* BR unifies f g *)
Compute @IsCommBinOpL ?[B] ?B ?B ?B ?[A]. (* BF does not unify *)

(** ** Left-Commutative Unary Operation over a Left Action *)

(** This has the same shape as [Z.mul_opp_r]. *)

Class IsCommL (A B : Type) (X : B -> B -> Prop)
  (f : B -> B) (k : A -> B -> B) : Prop :=
  comm_l (x : A) (y : B) : X (k x (f y)) (f (k x y)).

(** ** Commutativity of a Unary Operation and a Right Action *)

(** This has the same shape as [Z.mul_opp_l]. *)

Class IsCommR (A B : Type) (X : B -> B -> Prop)
  (f : B -> B) (k : B -> A -> B) : Prop :=
  comm_r (x : B) (y : A) : X (k (f x) y) (f (k x y)).

(** ** Commutativity of a Unary Operation and Actions *)

Class IsCommLR2 (A B : Type) (X : B -> B -> Prop)
  (f : B -> B) (k : A -> B -> B) (m : B -> A -> B) : Prop := {
  is_comm_l :> IsCommL X f k;
  is_comm_r :> IsCommR X f m;
}.

(** ** Commutativity of a Unary Operation and a Binary Operation *)

Class IsCommLR (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  is_comm_l_r_2 :> IsCommLR2 X f k k.

(** ** Commutative Form *)

Class IsCommForm (A B : Type) (X : A -> A -> Prop) (s : B -> B -> A) : Prop :=
  comm_form (x y : A) : X (s x y) (s y x).

(** ** Commutative Binary Operation *)

(** This has the same shape as [Z.mul_comm]. *)

Class IsCommBinOp (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  comm_bin_op (x y : A) : X (k x y) (k y x).

(** ** Commutative Unary Operation over a Unary Operation *)

Class IsCommUnOps (A : Type) (X : A -> A -> Prop) (f g : A -> A) : Prop :=
  comm_un_ops (x : A) : X (f (g x)) (g (f x)).

Section Context.

Context (A : Type) `(!@IsCommUnOps (A -> A) (A -> A) _=_ _o_).

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

#[local] Instance comm_l_is_comm `(!IsCommL _=_ f k) : IsCommUnOps _=_ f (k x).
Proof.
  intros y.
  pose proof comm_l (X := _=_) x y as a.
  rewrite a.
  reflexivity. Qed.

#[local] Instance comm_r_is_comm `(!IsCommR _=_ f k) :
  IsCommUnOps _=_ f (flip k x).
Proof.
  intros y.
  unfold flip.
  pose proof comm_r (X := _=_) y x as a.
  rewrite a.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve comm_l_is_comm comm_r_is_comm : typeclass_instances.
