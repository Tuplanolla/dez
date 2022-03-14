(** * Unitality *)

From DEZ Require Export
  Init.

(** ** Left-Unital Element of a Binary Function *)

Fail Fail Class IsUnlElemBinFnL (A B C : Type) (X : C -> C -> Prop)
  (x : B) (y : C) (k : B -> A -> C) : Prop :=
  unl_elem_bin_fn_l (z : A) : X (k x z) y.

(** ** Right-Unital Element of a Binary Function *)

Fail Fail Class IsUnlElemBinFnR (A B C : Type) (X : C -> C -> Prop)
  (x : B) (y : C) (k : A -> B -> C) : Prop :=
  unl_elem_bin_fn_r (z : A) : X (k z x) y.

(** ** Left-Unital Element of a Left Action *)
(** ** Left-Unital Element of an Action *)

Class IsUnlElemActL (A B : Type) (X : B -> B -> Prop)
  (x : A) (al : A -> B -> B) : Prop :=
  unl_elem_act_l (a : B) : X (al x a) a.

(** ** Right-Unital Element of a Right Action *)
(** ** Right-Unital Element of an Action *)

Class IsUnlElemActR (A B : Type) (X : B -> B -> Prop)
  (x : A) (ar : B -> A -> B) : Prop :=
  unl_elem_act_r (a : B) : X (ar a x) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (x : A) (al : A -> B -> B).

(** A left-unital element of an action is a special case
    of a right-unital element of its flipped version. *)

#[export] Instance unl_elem_act_l_is_unl_elem_act_r_flip
  `{!IsUnlElemActL X x al} : IsUnlElemActR X x (flip al).
Proof. intros a. unfold flip in *. eauto. Qed.

#[local] Instance unl_elem_act_r_flip_is_unl_elem_act_l
  `{!IsUnlElemActR X x (flip al)} : IsUnlElemActL X x al.
Proof. intros a. unfold flip in *. eauto. Qed.

End Context.

(** ** Left-Unital Element of a Binary Operation *)

(** This has the same shape as [Z.add_0_l]. *)

Class IsUnlElemL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  unl_elem_l (y : A) : X (k x y) y.

(** ** Right-Unital Element of a Binary Operation *)

(** This has the same shape as [Z.add_0_r]. *)

Class IsUnlElemR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  unl_elem_r (y : A) : X (k y x) y.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A).

(** A left-unital element of a binary operation is a special case
    of a right-unital element of its flipped version. *)

#[export] Instance unl_elem_l_is_unl_elem_r_flip
  `{!IsUnlElemL X x k} : IsUnlElemR X x (flip k).
Proof. intros y. unfold flip in *. eauto. Qed.

#[local] Instance unl_elem_r_flip_is_unl_elem_l
  `{!IsUnlElemR X x (flip k)} : IsUnlElemL X x k.
Proof. intros y. unfold flip in *. eauto. Qed.

End Context.

(** ** Unital Element of a Binary Operation *)

Class IsUnlElem (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  unl_elem_is_unl_elem_l :> IsUnlElemL X x k;
  unl_elem_is_unl_elem_r :> IsUnlElemR X x k;
}.
