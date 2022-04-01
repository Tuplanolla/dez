(** * Boundedness *)

From DEZ Require Export
  Init.

(** ** Lower Bound *)

Class IsLowerBnd (A : Type) (X : A -> A -> Prop)
  (x : A) : Prop :=
  lower_bnd (y : A) : X x y.

(** ** Upper Bound *)

Class IsUpperBnd (A : Type) (X : A -> A -> Prop)
  (x : A) : Prop :=
  upper_bnd (y : A) : X y x.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A).

(** A lower bound with respect to a binary relation is a special case
    of an upper bound with respect to its flipped version. *)

#[local] Instance lower_bnd_is_upper_bnd_flip
  `{!IsLowerBnd X x} : IsUpperBnd (flip X) x.
Proof. intros y. unfold flip in *. eauto. Qed.

#[local] Instance upper_bnd_flip_is_lower_bnd
  `{!IsUpperBnd (flip X) x} : IsLowerBnd X x.
Proof. intros y. unfold flip in *. eauto. Qed.

End Context.

(** ** Bounded *)

Class IsBnd (A : Type) (X : A -> A -> Prop)
  (x y : A) : Prop := {
  bnd_is_lower_bnd :> IsLowerBnd X x;
  bnd_is_upper_bnd :> IsUpperBnd X y;
}.
