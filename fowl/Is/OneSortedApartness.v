From Maniunfold.Has Require Export
  ApartnessRelation.
From Maniunfold.Is Require Export
  Cotransitive Irreflexive Symmetric.

Class IsApart (A : Type) `(HasApartRel A) : Prop := {
  A_apart_rel_is_cotrans :> IsCotrans apart_rel;
  A_apart_rel_is_irrefl :> IsIrrefl apart_rel;
  A_apart_rel_is_sym :> IsSym apart_rel;
}.
