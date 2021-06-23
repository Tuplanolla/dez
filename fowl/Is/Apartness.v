(** * Apartness or Constructive Inequality *)

From Maniunfold.Has Require Export
  ApartnessRelation.
From Maniunfold.Is Require Export
  Irreflexive Symmetric Cotransitive.
From Maniunfold.ShouldHave Require Export
  ApartnessRelationNotations.

Class IsApart (A : Type) (HR : HasApartRel A) : Prop := {
  is_irrefl :> IsIrrefl _#_;
  is_sym :> IsSym _#_;
  is_cotrans :> IsCotrans _#_;
}.
