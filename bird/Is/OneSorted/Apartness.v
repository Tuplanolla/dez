From Maniunfold.Has Require Export
  OneSorted.ApartnessRelation.
From Maniunfold.Is Require Export
  Cotransitive Irreflexive Symmetric.

Class IsApart (A : Type) (A_has_apart_rel : HasApartRel A) : Prop := {
  A_apart_rel_is_cotrans :> IsCotrans A apart_rel;
  A_apart_rel_is_irrefl :> IsIrrefl A apart_rel;
  A_apart_rel_is_sym :> IsSym A apart_rel;
}.
