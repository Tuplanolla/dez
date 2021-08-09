(** * Strict Partial Order *)

From DEZ.Has Require Export
  OrderRelations.
From DEZ.Is Require Export
  Irreflexive Transitive.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

Fail Fail Class IsStrPartOrd (A : Type) (HR : HasOrdRel A) : Prop := {
  is_irrefl :> IsIrrefl _<=_;
  is_trans :> IsTrans _<=_;
}.

Notation IsStrPartOrd := StrictOrder.
