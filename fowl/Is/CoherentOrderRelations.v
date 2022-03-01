(** * Coherence of an Order Relation and a Strict Order Relation *)

From DEZ.Has Require Export
  OrderRelations.
From DEZ.Supports Require Import
  OrderNotations.

(** This has the same shape as [le_neq]. *)

Class IsCohOrdRels (A : Type)
  (HR : HasOrdRel A) (HS : HasStrOrdRel A) : Prop :=
  coh_ord_rels (x y : A) : x < y <-> x <= y /\ x <> y.
