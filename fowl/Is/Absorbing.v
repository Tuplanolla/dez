(** * Absorptivity *)

From DEZ.Is Require Export
  Fixed.

(** ** Right Absorbing Element of Left Action *)
(** ** Right Annihilating Element of Left Action *)

Class IsAbsorbElemActL (A B : Type) (X : B -> B -> Prop)
  (a : B) (al : A -> B -> B) : Prop :=
  absorb_elem_act_l (x : A) : X (al x a) a.

(** ** Left Absorbing Element of Right Action *)
(** ** Left Annihilating Element of Right Action *)

Class IsAbsorbElemActR (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B) : Prop :=
  absorb_elem_act_r (x : A) : X (ar a x) a.

(** ** Right Absorbing Element of Binary Operation *)
(** ** Right Annihilating Element of Binary Operation *)

(** This has the same shape as [Z.mul_0_r]. *)

Class IsAbsorbElemL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_l (y : A) : X (k y x) x.

(** ** Left Absorbing Element of Binary Operation *)
(** ** Left Annihilating Element of Binary Operation *)

(** This has the same shape as [Z.mul_0_l]. *)

Class IsAbsorbElemR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_r (y : A) : X (k x y) x.

(** ** Absorbing Element of Binary Operation *)

Class IsAbsorbElem (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  absorb_elem_is_absorb_elem_l :> IsAbsorbElemL X x k;
  absorb_elem_is_absorb_elem_r :> IsAbsorbElemR X x k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (x : A) (k : A -> A -> A).

(** Right absorbing elements are fixed points. *)

#[export] Instance absorb_elem_l_is_fixed
  `{!IsAbsorbElemL X x k} (y : A) : IsFixed X x (k y).
Proof. apply absorb_elem_l. Qed.

(** Same in reverse. *)

#[local] Instance fixed_is_absorb_elem_l
  `{!forall y : A, IsFixed X x (k y)} : IsAbsorbElemL X x k.
Proof. intros y. apply fixed. Qed.

End Context.
