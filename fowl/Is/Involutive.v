(** * Involutivity *)

From DEZ Require Export
  Init.

(** ** Involutive Function *)

Class IsInvol (A : Type) (R : A -> A -> Prop) (f : A -> A) : Prop :=
  invol (x : A) : R (f (f x)) x.
