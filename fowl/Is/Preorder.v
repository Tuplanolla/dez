(** * Preorder *)

From Maniunfold.Has Require Export
  OrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.
From Maniunfold.Is Require Export
  Reflexive Transitive.

Fail Fail Class IsPreord (A : Type) (R : HasOrdRel A) : Prop := {
  is_refl :> IsRefl _<=_;
  is_trans :> IsTrans _<=_;
}.

Notation IsPreord := PreOrder.
