(** * Apartness or Constructive Inequality *)

From DEZ.Has Require Export
  ApartnessRelation.
From DEZ.Is Require Export
  Irreflexive Symmetric Cotransitive.
From DEZ.ShouldHave Require Export
  ApartnessRelationNotations.

Class IsApart (A : Type) (HR : HasApartRel A) : Prop := {
  is_irrefl :> IsIrrefl _#_;
  is_sym :> IsSym _#_;
  is_cotrans :> IsCotrans _#_;
}.
