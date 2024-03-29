(** * Absorptivity *)

From DEZ.Is Require Export
  Fixed.

(** ** Left-Absorbing Element of a Binary Function *)

Fail Fail Class IsAbsorbElemBinFnL (A B C : Type) (X : C -> C -> Prop)
  (x : B) (y : C) (k : B -> A -> C) : Prop :=
  absorb_elem_bin_fn_l (z : A) : X (k x z) y.

(** ** Right-Absorbing Element of a Binary Function *)

Fail Fail Class IsAbsorbElemBinFnR (A B C : Type) (X : C -> C -> Prop)
  (x : B) (y : C) (k : A -> B -> C) : Prop :=
  absorb_elem_bin_fn_r (z : A) : X (k z x) y.

(** ** Left-Absorbing Element of an Action *)
(** ** Left-Absorbing Element of a Left Action *)

Fail Fail Class IsAbsorbElemActL (A B : Type) (X : B -> B -> Prop)
  (x : A) (a : B) (al : A -> B -> B) : Prop :=
  absorb_elem_act_l (b : B) : X (al x b) a.

(** ** Left-Absorbing Element of a Right Action *)

Class IsAbsorbElemActRL (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B) : Prop :=
  absorb_elem_act_r_l (x : A) : X (ar a x) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B).

(** A left-absorbing element of a right action
    is a special case of a fixed point of its flipped partial application. *)

#[export] Instance absorb_elem_act_r_l_is_fixed_flip
  `{!IsAbsorbElemActRL X a ar} (x : A) : IsFixed X a (flip ar x).
Proof. hnf. unfold flip. apply absorb_elem_act_r_l. Qed.

#[local] Instance fixed_flip_is_absorb_elem_act_r_l
  `{!forall x : A, IsFixed X a (flip ar x)} : IsAbsorbElemActRL X a ar.
Proof.
  intros x.
  change (ar a x) with (flip ar x a).
  apply fixed.
Qed.

End Context.

(** ** Right-Absorbing Element of an Action *)
(** ** Right-Absorbing Element of a Right Action *)

Fail Fail Class IsAbsorbElemActR (A B : Type) (X : B -> B -> Prop)
  (x : A) (a : B) (ar : B -> A -> B) : Prop :=
  absorb_elem_act_r (b : B) : X (ar b x) a.

(** ** Right-Absorbing Element of a Left Action *)

Class IsAbsorbElemActLR (A B : Type) (X : B -> B -> Prop)
  (a : B) (al : A -> B -> B) : Prop :=
  absorb_elem_act_l_r (x : A) : X (al x a) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (a : B) (al : A -> B -> B).

(** A right-absorbing element of a left action
    is a special case of a fixed point of its partial application. *)

#[export] Instance absorb_elem_act_l_r_is_fixed
  `{!IsAbsorbElemActLR X a al} (x : A) : IsFixed X a (al x).
Proof. apply absorb_elem_act_l_r. Qed.

#[local] Instance fixed_is_absorb_elem_act_l_r
  `{!forall x : A, IsFixed X a (al x)} : IsAbsorbElemActLR X a al.
Proof. intros x. apply fixed. Qed.

End Context.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B).

(** A left-absorbing element of a right action is a special case
    of a right-absorbing element of its flipped version. *)

#[local] Instance absorb_elem_act_r_l_is_absorb_elem_act_l_r_flip
  `{!IsAbsorbElemActRL X a ar} : IsAbsorbElemActLR X a (flip ar).
Proof. intros x. unfold flip in *. eauto. Qed.

#[local] Instance absorb_elem_act_l_r_flip_is_absorb_elem_act_r_l
  `{!IsAbsorbElemActLR X a (flip ar)} : IsAbsorbElemActRL X a ar.
Proof. intros x. unfold flip in *. eauto. Qed.

End Context.

(** ** Left-Absorbing Element of a Binary Operation *)

(** This has the same shape as [Z.mul_0_l]. *)

Class IsAbsorbElemL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_l (y : A) : X (k x y) x.

(** ** Right-Absorbing Element of a Binary Operation *)

(** This has the same shape as [Z.mul_0_r]. *)

Class IsAbsorbElemR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_r (y : A) : X (k y x) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A).

(** A left-absorbing element of a binary operation is a special case
    of a right-absorbing element of its flipped version. *)

#[local] Instance absorb_elem_l_is_absorb_elem_act_r_flip
  `{!IsAbsorbElemL X x k} : IsAbsorbElemR X x (flip k).
Proof. intros y. unfold flip in *. eauto. Qed.

#[local] Instance absorb_elem_r_flip_is_absorb_elem_l
  `{!IsAbsorbElemR X x (flip k)} : IsAbsorbElemL X x k.
Proof. intros y. unfold flip in *. eauto. Qed.

End Context.

(** ** Absorbing Element of a Binary Operation *)
(** ** Annihiliating Element of a Binary Operation *)

Class IsAbsorbElem (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  absorb_elem_is_absorb_elem_l :> IsAbsorbElemL X x k;
  absorb_elem_is_absorb_elem_r :> IsAbsorbElemR X x k;
}.
