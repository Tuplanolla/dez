(** * Apartness *)

From DEZ.Is Require Export
  Irreflexive Symmetric Cotransitive.

(** ** Aparness Relation *)
(** ** Constructive Disequality *)

Class IsApart (A : Type) (X : A -> A -> Prop) : Prop := {
  apart_is_irrefl :> IsIrrefl X;
  apart_is_sym :> IsSym X;
  apart_is_cotrans :> IsCotrans X;
}.
