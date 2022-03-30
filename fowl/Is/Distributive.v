(** * Distributivity *)

From DEZ.Is Require Export
  Proper Injective Reflexive.

(** ** Unary Functions Distributing over Binary Functions *)

Class IsDistrUnFns (A0 A1 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (f : A0 -> B0) (g : A1 -> B1) (k : A0 -> A1 -> B2)
  (h : B2 -> C) (m : B0 -> B1 -> C) : Prop :=
  distr_un_fns (x : A0) (y : A1) : X (h (k x y)) (m (f x) (g y)).

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B).

(** Properness is a special case of distributivity. *)

#[local] Instance proper_is_distr_un_fns_impl_id
  `{!IsProper (X ==> Y) f} : IsDistrUnFns impl f f X id Y.
Proof. auto. Qed.

#[local] Instance distr_un_fns_impl_id_is_proper
  `{!IsDistrUnFns impl f f X id Y} : IsProper (X ==> Y) f.
Proof. auto. Qed.

(** Injectivity is a special case of distributivity. *)

#[local] Instance inj_un_fn_is_distr_un_fns_flip_impl_id
  `{!IsInjUnFn X Y f} : IsDistrUnFns (flip impl) f f X id Y.
Proof. auto. Qed.

#[local] Instance distr_un_fns_flip_impl_id_is_inj_un_fn
  `{!IsDistrUnFns (flip impl) f f X id Y} : IsInjUnFn X Y f.
Proof. auto. Qed.

End Context.

(** ** Unary Function Distributing over Binary Operations *)

Class IsDistrUnFn (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B) : Prop :=
  distr_un_fn (x y : A) : X (f (k x y)) (m (f x) (f y)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B).

(** Distributivity of a unary function over a binary operation
    is a special case of their distributivity as functions. *)

#[export] Instance distr_un_fn_is_distr_un_fns
  `{!IsDistrUnFn X f k m} : IsDistrUnFns X f f k f m.
Proof. auto. Qed.

#[local] Instance distr_un_fns_is_distr_un_fn
  `{!IsDistrUnFns X f f k f m} : IsDistrUnFn X f k m.
Proof. auto. Qed.

End Context.

(** ** Unary Functions Distributing over a Left Action *)

Class IsDistrUnFnL (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (al : A -> B -> B) : Prop :=
  distr_un_fn_l (x : A) (a : B) : X (g (al x a)) (al (f x) (g a)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (al : A -> B -> B).

(** Distributivity of unary functions over a left action
    is a special case of their distributivity as functions. *)

#[export] Instance distr_un_fn_l_is_distr_un_fns
  `{!IsDistrUnFnL X f g al} : IsDistrUnFns X f g al g al.
Proof. auto. Qed.

#[local] Instance distr_un_fns_is_distr_un_fn_l
  `{!IsDistrUnFns X f g al g al} : IsDistrUnFnL X f g al.
Proof. auto. Qed.

End Context.

(** ** Unary Functions Distributing over a Right Action *)

Class IsDistrUnFnR (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (ar : B -> A -> B) : Prop :=
  distr_un_fn_r (a : B) (x : A) : X (g (ar a x)) (ar (g a) (f x)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (ar : B -> A -> B).

(** Distributivity of unary functions over a right action
    is a special case of their distributivity as functions. *)

#[export] Instance distr_un_fn_r_is_distr_un_fns
  `{!IsDistrUnFnR X f g ar} : IsDistrUnFns X g f ar g ar.
Proof. auto. Qed.

#[local] Instance distr_un_fns_is_distr_un_fn_r
  `{!IsDistrUnFns X g f ar g ar} : IsDistrUnFnR X f g ar.
Proof. auto. Qed.

End Context.

(** ** Unary Operation Distributing over a Binary Operation *)

(** This has the same shape as [Z.opp_add_distr]. *)

Class IsDistrUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  distr_un_op (x y : A) : X (f (k x y)) (k (f x) (f y)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A).

(** Distributivity of a unary operation over a binary operation
    is a special case of their distributivity as functions. *)

#[export] Instance distr_un_op_is_distr_un_fns
  `{!IsDistrUnOp X f k} : IsDistrUnFns X f f k f k.
Proof. auto. Qed.

#[local] Instance distr_un_fns_is_distr_un_op
  `{!IsDistrUnFns X f f k f k} : IsDistrUnOp X f k.
Proof. auto. Qed.

End Context.

(** ** Binary Functions Left-Distributing over Binary Functions *)

Class IsDistrBinFnsL (A0 A1 A2 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (m : A0 -> A2 -> B1) (n : A1 -> A2 -> B2)
  (p : A0 -> B2 -> C) (q : B0 -> B1 -> C) : Prop :=
  distr_bin_fns_l (x : A0) (y : A1) (z : A2) :
    X (p x (n y z)) (q (k x y) (m x z)).

Section Context.

Context (A0 A1 A2 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (m : A0 -> A2 -> B1) (n : A1 -> A2 -> B2)
  (p : A0 -> B2 -> C) (q : B0 -> B1 -> C).

(** Left-distributivity of binary functions over binary functions
    is a special case of the distributivity
    of their partially-applied versions. *)

#[export] Instance distr_bin_fns_l_is_distr_un_fns
  `{!IsDistrBinFnsL X k m n p q} (x : A0) :
  IsDistrUnFns X (k x) (m x) n (p x) q.
Proof. intros y z. apply distr_bin_fns_l. Qed.

#[local] Instance distr_un_fns_is_distr_bin_fns_l
  `{!forall x : A0, IsDistrUnFns X (k x) (m x) n (p x) q} :
  IsDistrBinFnsL X k m n p q.
Proof. intros x y z. apply distr_un_fns. Qed.

End Context.

(** ** Binary Functions Right-Distributing over Binary Functions *)

Class IsDistrBinFnsR (A0 A1 A2 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A2 -> B0) (m : A1 -> A2 -> B1) (n : A0 -> A1 -> B2)
  (p : B2 -> A2 -> C) (q : B0 -> B1 -> C) : Prop :=
  distr_bin_fns_r (x : A0) (y : A1) (z : A2) :
    X (p (n x y) z) (q (k x z) (m y z)).

Section Context.

Context (A0 A1 A2 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A2 -> B0) (m : A1 -> A2 -> B1) (n : A0 -> A1 -> B2)
  (p : B2 -> A2 -> C) (q : B0 -> B1 -> C).

(** Right-distributivity of binary functions over binary functions
    is a special case of the distributivity
    of their flipped partially-applied versions. *)

#[export] Instance distr_bin_fns_r_is_distr_un_fns
  `{!IsDistrBinFnsR X k m n p q} (z : A2) :
  IsDistrUnFns X (flip k z) (flip m z) n (flip p z) q.
Proof. intros x y. unfold flip. apply distr_bin_fns_r. Qed.

#[local] Instance distr_un_fns_is_distr_bin_fns_r
  `{!forall z : A2, IsDistrUnFns X (flip k z) (flip m z) n (flip p z) q} :
  IsDistrBinFnsR X k m n p q.
Proof.
  intros x y z.
  change (k x z) with (flip k z x).
  change (m y z) with (flip m z y).
  change (p (n x y) z) with (flip p z (n x y)).
  apply distr_un_fns. Qed.

End Context.

Section Context.

Context (A0 A1 A2 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (m : A0 -> A2 -> B1) (n : A1 -> A2 -> B2)
  (p : A0 -> B2 -> C) (q : B0 -> B1 -> C).

(** Left-distributivity of binary functions over binary functions
    is a special case of the right-distributivity of their flipped versions. *)

#[local] Instance distr_bin_fns_l_is_distr_bin_fns_r_flip
  `{!IsDistrBinFnsL X k m n p q} :
  IsDistrBinFnsR X (flip k) (flip m) n (flip p) q.
Proof. intros y z x. unfold flip in *. eauto. Qed.

#[local] Instance distr_bin_fns_r_flip_is_distr_bin_fns_l
  `{!IsDistrBinFnsR X (flip k) (flip m) n (flip p) q} :
  IsDistrBinFnsL X k m n p q.
Proof. intros x y z. unfold flip in *. eauto. Qed.

End Context.

(** ** Left Action Distributing over a Binary Operation *)

Class IsDistrActL (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B) (k : B -> B -> B) : Prop :=
  distr_act_l (x : A) (a b : B) : X (al x (k a b)) (k (al x a) (al x b)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B) (k : B -> B -> B).

(** Distributivity of a left action over a binary operation
    is a special case of their left-distributivity as binary functions. *)

#[export] Instance distr_act_l_is_distr_bin_fns_l
  `{!IsDistrActL X al k} : IsDistrBinFnsL X al al k al k.
Proof. auto. Qed.

#[local] Instance distr_bin_fns_l_is_distr_act_l
  `{!IsDistrBinFnsL X al al k al k} : IsDistrActL X al k.
Proof. auto. Qed.

End Context.

(** ** Right Action Distributing over a Binary Operation *)

Class IsDistrActR (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B) (k : B -> B -> B) : Prop :=
  distr_act_r (a b : B) (x : A) : X (ar (k a b) x) (k (ar a x) (ar b x)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B) (k : B -> B -> B).

(** Distributivity of a right action over a binary operation
    is a special case of their right-distributivity as binary functions. *)

#[export] Instance distr_act_r_is_distr_bin_fns_r
  `{!IsDistrActR X ar k} : IsDistrBinFnsR X ar ar k ar k.
Proof. auto. Qed.

#[local] Instance distr_bin_fns_r_is_distr_act_r
  `{!IsDistrBinFnsR X ar ar k ar k} : IsDistrActR X ar k.
Proof. auto. Qed.

End Context.

(** ** Binary Operation Left-Distributing over a Binary Operation *)

(** This has the same shape as [Z.mul_add_distr_l]. *)

Class IsDistrL (A : Type) (X : A -> A -> Prop) (k m : A -> A -> A) : Prop :=
  distr_l (x y z : A) : X (k x (m y z)) (m (k x y) (k x z)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (m : A -> A -> A).

(** Left-distributivity of a binary operation over a binary operation
    is a special case of their left-distributivity as binary functions. *)

#[export] Instance distr_l_is_distr_bin_fns_l
  `{!IsDistrL X k m} : IsDistrBinFnsL X k k m k m.
Proof. auto. Qed.

#[local] Instance distr_bin_fns_l_is_distr_l
  `{!IsDistrBinFnsL X k k m k m} : IsDistrL X k m.
Proof. auto. Qed.

End Context.

(** ** Binary Operation Right-Distributing over a Binary Operation *)

(** This has the same shape as [Z.mul_add_distr_r]. *)

Class IsDistrR (A : Type) (X : A -> A -> Prop) (k m : A -> A -> A) : Prop :=
  distr_r (x y z : A) : X (k (m x y) z) (m (k x z) (k y z)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (m : A -> A -> A).

(** Right-distributivity of a binary operation over a binary operation
    is a special case of their right-distributivity as binary functions. *)

#[export] Instance distr_r_is_distr_bin_fns_r
  `{!IsDistrR X k m} : IsDistrBinFnsR X k k m k m.
Proof. auto. Qed.

#[local] Instance distr_bin_fns_r_is_distr_r
  `{!IsDistrBinFnsR X k k m k m} : IsDistrR X k m.
Proof. auto. Qed.

End Context.

(** ** Binary Operation Distributing over a Binary Operation *)

Class IsDistr (A : Type) (X : A -> A -> Prop) (k m : A -> A -> A) : Prop := {
  distr_is_distr_l :> IsDistrL X k m;
  distr_is_distr_r :> IsDistrR X k m;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Identity distributes over everything. *)

#[export] Instance distr_un_op_id
  `{!IsRefl X} : IsDistrUnOp X id k.
Proof. intros x y. unfold id. reflexivity. Qed.

End Context.
