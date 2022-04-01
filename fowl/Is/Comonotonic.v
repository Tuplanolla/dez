(** * Comonotonicity *)

From DEZ Require Export
  Init.

(** ** Comonotonic Function *)

Class IsComono (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  comono (x y : A) (a : Y (f x) (f y)) : X x y.

(** ** Strictly Comonotonic Function *)

(** Strict comonotonicity with respect to an order relation is just
    comonotonicity with respect to the corresponding strict order relation. *)

Notation IsStrComono := IsComono (only parsing).
Notation str_comono := comono (only parsing).
