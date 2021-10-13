(** * Apartness *)

From DEZ.Is Require Export
  Irreflexive Symmetric Cotransitive.

(** ** Constructive Inequality *)

Class IsApart (A : Type) (R : A -> A -> Prop) : Prop := {
  is_irrefl :> IsIrrefl R;
  is_sym :> IsSym R;
  is_cotrans :> IsCotrans R;
}.
