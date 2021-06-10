(** * Strict Partial Order *)

From Maniunfold.Has Require Export
  OrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.
From Maniunfold.Is Require Export
  Irreflexive Transitive.

Fail Fail Class IsStrPartOrd (A : Type) (R : HasOrdRel A) : Prop := {
  is_irrefl :> IsIrrefl _<=_;
  is_trans :> IsTrans _<=_;
}.

Notation IsStrPartOrd := StrictOrder.
