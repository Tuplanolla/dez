(* * Commutativity *)

From DEZ Require Export
  Init.

(** ** Commutative Elements of a Form *)

Class IsCommElemsForm (A B : Type) (X : A -> A -> Prop)
  (s : B -> B -> A) (a b : B) : Prop :=
  comm_elems_form : X (s a b) (s b a).

(** ** Commutative Form *)

Class IsCommForm (A B : Type) (X : A -> A -> Prop) (s : B -> B -> A) : Prop :=
  comm_form (a b : B) : X (s a b) (s b a).

Section Context.

Context (A B : Type) (X : A -> A -> Prop)
  (s : B -> B -> A).

(** Commutative forms are forms with commutative elements. *)

#[export] Instance comm_form_is_comm_elems_form
  `{!IsCommForm X s} (a b : B) : IsCommElemsForm X s a b.
Proof. apply comm_form. Qed.

#[local] Instance comm_elems_form_is_comm_form
  `{!forall a b : B, IsCommElemsForm X s a b} : IsCommForm X s.
Proof. intros a b. apply comm_elems_form. Qed.

End Context.

(** ** Commutative Elements of a Binary Operation *)

Class IsCommElemsBinOp (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (x y : A) : Prop :=
  comm_elems_bin_op : X (k x y) (k y x).

(** ** Commutative Binary Operation *)

(** This has the same shape as [Z.mul_comm]. *)

Class IsCommBinOp (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  comm_bin_op (x y : A) : X (k x y) (k y x).

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Commutative binary operations
    are binary operations with commutative elements. *)

#[export] Instance comm_bin_op_is_comm_elems_bin_op
  `{!IsCommBinOp X k} (x y : A) : IsCommElemsBinOp X k x y.
Proof. apply comm_bin_op. Qed.

#[local] Instance comm_elems_bin_op_is_comm_bin_op
  `{!forall x y : A, IsCommElemsBinOp X k x y} : IsCommBinOp X k.
Proof. intros x y. apply comm_elems_bin_op. Qed.

End Context.

(** ** Commutative Unary Operations *)

Class IsCommUnOps (A : Type) (X : A -> A -> Prop) (f g : A -> A) : Prop :=
  comm_un_ops (x : A) : X (f (g x)) (g (f x)).

Section Context.

Context (A : Type) (X : A -> A -> Prop) (f g : A -> A).

(** Commutative unary operations are commutative elements
    of the endofunction monoid. *)

#[export] Instance comm_un_ops_is_comm_elems_bin_op_compose
  `{!IsCommUnOps X f g} : IsCommElemsBinOp (pointwise_relation _ X) _o_ f g.
Proof. intros x. unfold compose. apply comm_un_ops. Qed.

#[local] Instance comm_elems_bin_op_compose_is_comm_un_ops
  `{!IsCommElemsBinOp (pointwise_relation _ X) _o_ f g} : IsCommUnOps X f g.
Proof.
  intros x.
  change (f (g x)) with ((f o g) x).
  change (g (f x)) with ((g o f) x).
  pose proof comm_elems_bin_op x as a.
  apply a. Qed.

End Context.

(** ** Left-Commutative Binary Functions over Unary Functions *)

Class IsCommBinFnsL (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B1) (f : A0 -> B0)
  (m : B0 -> A1 -> C) (g : B1 -> C) : Prop :=
  comm_bin_fns_l (x : A0) (y : A1) : X (m (f x) y) (g (k x y)).

(** ** Right-Commutative Binary Functions over Unary Functions *)

Class IsCommBinFnsR (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (f : A1 -> B1)
  (m : A0 -> B1 -> C) (g : B0 -> C) : Prop :=
  comm_bin_fns_r (x : A0) (y : A1) : X (m x (f y)) (g (k x y)).

Section Context.

Context (A0 A1 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B1) (f : A0 -> B0)
  (m : B0 -> A1 -> C) (g : B1 -> C).

(** Left-commutativity of binary functions over unary functions
    is a special case of the right-commutativity of their flipped versions. *)

#[local] Instance comm_bin_fns_l_is_comm_bin_fns_r_flip
  `{!IsCommBinFnsL X k f m g} : IsCommBinFnsR X (flip k) f (flip m) g.
Proof. intros y x. unfold flip in *. eauto. Qed.

#[local] Instance comm_bin_fns_r_flip_is_comm_bin_fns_l
  `{!IsCommBinFnsR X (flip k) f (flip m) g} : IsCommBinFnsL X k f m g.
Proof. intros x y. unfold flip in *. eauto. Qed.

End Context.

(** ** Left-Commutative Right Actions over a Unary Function *)

Class IsCommActRsL (A B C : Type) (X : C -> C -> Prop)
  (ar : B -> A -> B) (f : B -> C) (br : C -> A -> C) : Prop :=
  comm_act_rs_l (a : B) (x : A) : X (br (f a) x) (f (ar a x)).

Section Context.

Context (A B C : Type) (X : C -> C -> Prop)
  (ar : B -> A -> B) (f : B -> C) (br : C -> A -> C).

(** Left-commutativity of right actions over a unary function
    is a special case of their left-commutativity
    as binary functions over unary functions. *)

#[export] Instance comm_act_rs_l_is_comm_bin_fns_l
  `{!IsCommActRsL X ar f br} : IsCommBinFnsL X ar f br f.
Proof. auto. Qed.

#[local] Instance comm_bin_fns_l_is_comm_act_rs_l
  `{!IsCommBinFnsL X ar f br f} : IsCommActRsL X ar f br.
Proof. auto. Qed.

End Context.

(** ** Right-Commutative Left Actions over a Unary Function *)

Class IsCommActLsR (A B C : Type) (X : C -> C -> Prop)
  (al : A -> B -> B) (f : B -> C) (bl : A -> C -> C) : Prop :=
  comm_act_ls_r (x : A) (a : B) : X (bl x (f a)) (f (al x a)).

Section Context.

Context (A B C : Type) (X : C -> C -> Prop)
  (al : A -> B -> B) (f : B -> C) (bl : A -> C -> C).

(** Right-commutativity of left actions over a unary function
    is a special case of their right-commutativity
    as binary functions over unary functions. *)

#[export] Instance comm_act_ls_r_is_comm_bin_fns_r
  `{!IsCommActLsR X al f bl} : IsCommBinFnsR X al f bl f.
Proof. auto. Qed.

#[local] Instance comm_bin_fns_r_is_comm_act_ls_r
  `{!IsCommBinFnsR X al f bl f} : IsCommActLsR X al f bl.
Proof. auto. Qed.

End Context.

(** ** Left-Commutative Binary Operation over a Unary Operation *)

(** This has the same shape as [Z.mul_opp_l]. *)

Class IsCommL (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A) : Prop :=
  comm_l (x y : A) : X (k (f x) y) (f (k x y)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A).

(** Left-commutativity of a binary operation over a unary operation
    is a special case of their left-commutativity
    as binary functions over unary functions. *)

#[export] Instance comm_l_is_comm_bin_fns_l
  `{!IsCommL X k f} : IsCommBinFnsL X k f k f.
Proof. auto. Qed.

#[local] Instance comm_bin_fns_l_is_comm_l
  `{!IsCommBinFnsL X k f k f} : IsCommL X k f.
Proof. auto. Qed.

(** Left-commutativity of a binary operation over a unary operation
    is a special case of the commutativity
    of its flipped partial application over the unary operation. *)

#[export] Instance comm_l_is_comm_un_ops_flip
  `{!IsCommL X k f} (x : A) : IsCommUnOps X (flip k x) f.
Proof. intros y. unfold flip. apply comm_l. Qed.

#[local] Instance comm_un_ops_flip_is_comm_l
  `{!forall x : A, IsCommUnOps X (flip k x) f} : IsCommL X k f.
Proof.
  intros x y.
  change (k x y) with (flip k y x).
  change (k (f x) y) with (flip k y (f x)).
  apply comm_un_ops. Qed.

End Context.

(** ** Right-Commutative Binary Operation over a Unary Operation *)

(** This has the same shape as [Z.mul_opp_r]. *)

Class IsCommR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A) : Prop :=
  comm_r (x y : A) : X (k x (f y)) (f (k x y)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A).

(** Right-commutativity of a binary operation over a unary operation
    is a special case of their right-commutativity
    as binary functions over unary functions. *)

#[export] Instance comm_r_is_comm_bin_fns_r
  `{!IsCommR X k f} : IsCommBinFnsR X k f k f.
Proof. auto. Qed.

#[local] Instance comm_bin_fns_r_is_comm_r
  `{!IsCommBinFnsR X k f k f} : IsCommR X k f.
Proof. auto. Qed.

(** Right-commutativity of a binary operation over a unary operation
    is a special case of the commutativity
    of its partial application over the unary operation. *)

#[export] Instance comm_r_is_comm_un_ops
  `{!IsCommR X k f} (x : A) : IsCommUnOps X (k x) f.
Proof. intros y. apply comm_r. Qed.

#[local] Instance comm_un_ops_is_comm_r
  `{!forall x : A, IsCommUnOps X (k x) f} : IsCommR X k f.
Proof. intros x y. apply comm_un_ops. Qed.

End Context.

(** ** Commutative Binary Operation over a Unary Operation *)

Class IsComm (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (f : A -> A) : Prop := {
  comm_is_comm_l :> IsCommL X k f;
  comm_is_comm_r :> IsCommR X k f;
}.
