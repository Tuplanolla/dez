(* bad *)
From Maniunfold.Has.OneSorted Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Preorder Antisymmetric.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsPartOrd (A : Type) (A_has_ord_rel : HasOrdRel A) : Prop := {
  A_ord_rel_is_antisym :> IsAntisym A ord_rel;
  A_ord_rel_is_preord :> IsPreord A ord_rel;
}.
