(* * Commutativity *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From DEZ.Has Require Export
  Forms Operations.

(** ** Commutative Unary Operations *)

Class IsCommUnOps (A : Type) (X : A -> A -> Prop) (f g : A -> A) : Prop :=
  comm_un_ops (x : A) : X (f (g x)) (g (f x)).

(** ** Left-Commutative Binary Functions over Unary Functions *)

Class IsCommBinFnsL (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B1) (f : A0 -> B0)
  (g : B1 -> C) (m : B0 -> A1 -> C) : Prop :=
  comm_bin_fns_l (x : A0) (y : A1) : X (m (f x) y) (g (k x y)).

(** ** Right-Commutative Binary Functions over Unary Functions *)

Class IsCommBinFnsR (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (f : A1 -> B1)
  (g : B0 -> C) (m : A0 -> B1 -> C) : Prop :=
  comm_bin_fns_r (x : A0) (y : A1) : X (m x (f y)) (g (k x y)).

(** ** Left-Commutative Right Actions over a Unary Function *)

Class IsCommActRsL (A B C : Type) (X : C -> C -> Prop)
  (ar : B -> A -> B) (f : B -> C) (br : C -> A -> C) : Prop :=
  comm_act_rs_l (a : B) (x : A) : X (br (f a) x) (f (ar a x)).

(** ** Right-Commutative Left Actions over a Unary Function *)

Class IsCommActLsR (A B C : Type) (X : C -> C -> Prop)
  (al : A -> B -> B) (f : B -> C) (bl : A -> C -> C) : Prop :=
  comm_act_ls_r (x : A) (a : B) : X (bl x (f a)) (f (al x a)).

(** ** Left-Commutative Binary Operation over a Unary Operation *)

(** This has the same shape as [Z.mul_opp_l]. *)

Class IsCommL (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A) : Prop :=
  comm_l (x y : A) : X (k (f x) y) (f (k x y)).

(** ** Right-Commutative Binary Operation over a Unary Operation *)

(** This has the same shape as [Z.mul_opp_r]. *)

Class IsCommR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A) : Prop :=
  comm_r (x y : A) : X (k x (f y)) (f (k x y)).

(** ** Commutative Binary Operation over a Unary Operation *)

Class IsComm (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A) : Prop := {
  comm_is_comm_l :> IsCommL X k f;
  comm_is_comm_r :> IsCommR X k f;
}.

(** ** Commutative Form *)

Class IsCommForm (A B : Type) (X : A -> A -> Prop) (s : B -> B -> A) : Prop :=
  comm_form (x y : B) : X (s x y) (s y x).

(** ** Commutative Binary Operation *)

(** This has the same shape as [Z.mul_comm]. *)

Class IsCommBinOp (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  comm_bin_op (x y : A) : X (k x y) (k y x).

(** TODO Hierarchy and these instances. *)

Section Context.

Context (A : Type) (X : A -> A -> Prop).

#[export] Instance comm_un_ops_is_comm_bin_op_compose
  `{!forall f g : A -> A, IsCommUnOps X f g} :
  IsCommBinOp (pointwise_relation _ X) _o_.
Proof. intros f g x. unfold compose. apply comm_un_ops. Qed.

#[local] Instance comm_bin_op_compose_is_comm_un_ops
  `{!IsCommBinOp (pointwise_relation _ X) _o_} (f g : A -> A) :
  IsCommUnOps X f g.
Proof.
  intros x.
  change (f (g x)) with ((f o g) x).
  change (g (f x)) with ((g o f) x).
  pose proof comm_bin_op f g x as a.
  assumption. Qed.

End Context.

Section Context.

Context (A : Type) (x : A) (f : A -> A) (k : A -> A -> A).

(** Chiral commutativity is just commutativity of partial applications. *)

#[local] Instance comm_r_is_comm_un_ops `(!IsCommR _=_ k f) : IsCommUnOps _=_ f (k x).
Proof.
  intros y.
  pose proof comm_r (X := _=_) x y as a.
  rewrite a.
  reflexivity. Qed.

#[local] Instance comm_l_is_comm_u_ops `(!IsCommL _=_ k f) :
  IsCommUnOps _=_ (flip k x) f.
Proof.
  intros y.
  unfold flip.
  pose proof comm_l (X := _=_) y x as a.
  rewrite a.
  reflexivity. Qed.

End Context.
