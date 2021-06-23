(** * Strict Partial Order *)

From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.Is Require Export
  Irreflexive Transitive.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Fail Fail Class IsStrPartOrd (A : Type) (HR : HasOrdRel A) : Prop := {
  is_irrefl :> IsIrrefl _<=_;
  is_trans :> IsTrans _<=_;
}.

Notation IsStrPartOrd := StrictOrder.
