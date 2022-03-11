(** * Inflationarity *)

From DEZ Require Export
  Init.

(** ** Inflationary Unary Operation *)
(** ** Progressive Unary Operation *)

Class IsInflUnOp (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  infl_un_op (x : A) : X x (f x).

(** ** Inflationary Left Action *)

Class IsInflActL (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B) : Prop :=
  infl_act_l (x : A) (a : B) : X a (al x a).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B).

(** Inflationarity of a left action is a special case
    of the inflationarity of its partial application. *)

#[export] Instance infl_act_l_is_infl_un_op
  `{!IsInflActL X al} (x : A) : IsInflUnOp X (al x).
Proof. intros a. apply infl_act_l. Qed.

#[local] Instance infl_un_op_is_infl_act_l
  `{!forall x : A, IsInflUnOp X (al x)} : IsInflActL X al.
Proof. intros x a. apply infl_un_op. Qed.

End Context.

(** ** Inflationary Right Action *)

Class IsInflActR (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B) : Prop :=
  infl_act_r (a : B) (x : A) : X a (ar a x).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B).

(** Inflationarity of a left action is a special case
    of the inflationarity of its flipped partial application. *)

#[export] Instance infl_act_r_is_infl_un_op_flip
  `{!IsInflActR X ar} (x : A) : IsInflUnOp X (flip ar x).
Proof. intros a. unfold flip. apply infl_act_r. Qed.

#[local] Instance infl_un_op_flip_is_infl_act_r
  `{!forall x : A, IsInflUnOp X (flip ar x)} : IsInflActR X ar.
Proof.
  intros x a.
  change (ar x a) with (flip ar a x).
  apply infl_un_op. Qed.

End Context.

(** ** Left-Inflationary Binary Operation *)

Class IsInflL (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  infl_l (x y : A) : X y (k x y).

(** ** Right-Inflationary Binary Operation *)

Class IsInflR (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  infl_r (x y : A) : X x (k x y).

(** ** Inflationary Binary Operation *)

Class IsInfl (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  infl_is_infl_l :> IsInflL X k;
  infl_is_infl_r :> IsInflR X k;
}.
