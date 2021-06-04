(** * Coherence of a Lax and a Strict Order Relation *)

From Maniunfold.Has Require Export
  OrderRelation StrictOrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.

(** This is analogous in structure to [le_neq]. *)

Class IsCohOrdRels (A : Type)
  (R : HasOrdRel A) (S : HasStrictOrdRel A) : Prop :=
  coh_ord_rels (x y : A) : x < y <-> x <= y /\ x <> y.
