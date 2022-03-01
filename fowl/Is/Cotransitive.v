(** * Cotransitivity *)

From DEZ Require Export
  Init.

(** ** Cotransitive Binary Relation *)

Class IsCotrans (A : Type) (X : A -> A -> Prop) : Prop :=
  cotrans (x y z : A) (a : X x z) : X x y \/ X y z.
