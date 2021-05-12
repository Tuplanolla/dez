(* bad *)
From Maniunfold.Has Require Export
  OneSortedEquivalenceRelation OneSortedOrderRelation.
From Maniunfold.Is Require Export
  OneSortedPreorder Antisymmetric.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Class IsPartOrd (A : Type) `(HasOrdRel A) : Prop := {
  A_ord_rel_is_antisym :> IsAntisym ord_rel;
  A_ord_rel_is_preord :> IsPreord ord_rel;
}.
