(** * Deflationarity *)

From DEZ Require Export
  Init.

(** ** Deflationary Unary Operation *)
(** ** Regressive Unary Operation *)

Class IsDeflUnOp (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  defl_un_op (x : A) : X (f x) x.

(** ** Deflationary Left Action *)

Class IsDeflActL (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B) : Prop :=
  defl_act_l (x : A) (a : B) : X (al x a) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B).

(** Deflationarity of a left action is a special case
    of the deflationarity of its partial application. *)

#[export] Instance defl_act_l_is_defl_un_op
  `{!IsDeflActL X al} (x : A) : IsDeflUnOp X (al x).
Proof. intros a. apply defl_act_l. Qed.

#[local] Instance defl_un_op_is_defl_act_l
  `{!forall x : A, IsDeflUnOp X (al x)} : IsDeflActL X al.
Proof. intros x a. apply defl_un_op. Qed.

End Context.

(** ** Deflationary Right Action *)

Class IsDeflActR (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B) : Prop :=
  defl_act_r (a : B) (x : A) : X (ar a x) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B).

(** Deflationarity of a left action is a special case
    of the deflationarity of its flipped partial application. *)

#[export] Instance defl_act_r_is_defl_un_op_flip
  `{!IsDeflActR X ar} (x : A) : IsDeflUnOp X (flip ar x).
Proof. intros a. unfold flip. apply defl_act_r. Qed.

#[local] Instance defl_un_op_flip_is_defl_act_r
  `{!forall x : A, IsDeflUnOp X (flip ar x)} : IsDeflActR X ar.
Proof.
  intros x a.
  change (ar x a) with (flip ar a x).
  apply defl_un_op. Qed.

End Context.

(** ** Left-Deflationary Binary Operation *)

Class IsDeflL (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  defl_l (x y : A) : X (k x y) y.

(** ** Right-Deflationary Binary Operation *)

Class IsDeflR (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  defl_r (x y : A) : X (k x y) x.

(** ** Deflationary Binary Operation *)

Class IsDefl (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  defl_is_defl_l :> IsDeflL X k;
  defl_is_defl_r :> IsDeflR X k;
}.
