(** * Involutivity *)

From DEZ Require Export
  Init.

(** ** Involutive Function *)

Class IsInvol (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  invol (x : A) : X (f (f x)) x.
