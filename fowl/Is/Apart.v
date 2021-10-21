(** * Apartness *)

From DEZ.Is Require Export
  Irreflexive Symmetric Cotransitive.

(** ** Constructive Inequality *)

Class IsApart (A : Type) (X : A -> A -> Prop) : Prop := {
  is_irrefl :> IsIrrefl X;
  is_sym :> IsSym X;
  is_cotrans :> IsCotrans X;
}.
