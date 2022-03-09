(** * Absorptivity *)

From DEZ.Is Require Export
  Fixed.

(** TODO Missing instances. *)

(** ** Left-Absorbing Element of a Binary Function *)

Class IsAbsorbElemBinFnL (A0 A1 B : Type) (X : B -> B -> Prop)
  (x : A0) (y : B) (k : A0 -> A1 -> B) : Prop :=
  absorb_elem_bin_fn_l (z : A1) : X (k x z) y.

(** ** Right-Absorbing Element of a Binary Function *)

Class IsAbsorbElemBinFnR (A0 A1 B : Type) (X : B -> B -> Prop)
  (x : A1) (y : B) (k : A0 -> A1 -> B) : Prop :=
  absorb_elem_bin_fn_r (z : A0) : X (k z x) y.

Section Context.

Context (A0 A1 B : Type) (X : B -> B -> Prop)
  (x : A0) (y : B) (k : A0 -> A1 -> B).

(** A right-absorbing element of a flipped binary function
    is a special case of a left-absorbing element of a binary function. *)

#[export] Instance absorb_elem_bin_fn_l_is_absorb_elem_bin_fn_r
  `{!IsAbsorbElemBinFnL X x y k} : IsAbsorbElemBinFnR X x y (flip k).
Proof. intros z. unfold flip. apply absorb_elem_bin_fn_l. Qed.

#[local] Instance absorb_elem_bin_fn_r_is_absorb_elem_bin_fn_l
  `{!IsAbsorbElemBinFnR X x y (flip k)} : IsAbsorbElemBinFnL X x y k.
Proof.
  intros z.
  change (k x z) with (flip k z x).
  apply absorb_elem_bin_fn_r. Qed.

End Context.

(** ** Left-Absorbing Element of an Action *)
(** ** Left-Absorbing Element of a Left Action *)

Class IsAbsorbElemActL (A B : Type) (X : B -> B -> Prop)
  (a b : B) (al : A -> B -> B) : Prop :=
  absorb_elem_act_l (y : A) : X (al y a) b.

(** ** Right-Absorbing Element of a Left Action *)

Class IsAbsorbElemActLR (A B : Type) (X : B -> B -> Prop)
  (a : B) (al : A -> B -> B) : Prop :=
  absorb_elem_act_l_r (x : A) : X (al x a) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (a : B) (al : A -> B -> B).

(** Fixed point of a partially-applied left action
    is a special case of its right-absorbing element. *)

#[export] Instance absorb_elem_act_l_r_is_fixed
  `{!IsAbsorbElemActLR X a al} (x : A) : IsFixed X a (al x).
Proof. apply absorb_elem_act_l_r. Qed.

#[local] Instance fixed_is_absorb_elem_act_l_r
  `{!forall x : A, IsFixed X a (al x)} : IsAbsorbElemActLR X a al.
Proof. intros x. apply fixed. Qed.

End Context.

(** ** Left-Absorbing Element of a Right Action *)

Class IsAbsorbElemActRL (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B) : Prop :=
  absorb_elem_act_r_l (x : A) : X (ar a x) a.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B).

(** Fixed point of a partially-applied flipped right action
    is a special case of its left-absorbing element. *)

#[export] Instance absorb_elem_act_r_l_is_fixed_flip
  `{!IsAbsorbElemActRL X a ar} (x : A) : IsFixed X a (flip ar x).
Proof. hnf. unfold flip. apply absorb_elem_act_r_l. Qed.

#[local] Instance fixed_flip_is_absorb_elem_act_r_l
  `{!forall x : A, IsFixed X a (flip ar x)} : IsAbsorbElemActRL X a ar.
Proof.
  intros x.
  change (ar a x) with (flip ar x a).
  apply fixed. Qed.

End Context.

(** ** Right-Absorbing Element of an Action *)
(** ** Right-Absorbing Element of a Right Action *)

Class IsAbsorbElemActR (A B : Type) (X : B -> B -> Prop)
  (a b : B) (ar : B -> A -> B) : Prop :=
  absorb_elem_act_r (x : A) : X (ar a x) b.

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

(** ** Absorbing Element of a Binary Operation *)
(** ** Annihiliating Element of a Binary Operation *)

Class IsAbsorbElem (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  absorb_elem_is_absorb_elem_l :> IsAbsorbElemL X x k;
  absorb_elem_is_absorb_elem_r :> IsAbsorbElemR X x k;
}.
