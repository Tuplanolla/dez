(** * Preorder *)

From DEZ.Has Require Export
  OrderRelations.
From DEZ.Is Require Export
  Reflexive Transitive.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

Fail Fail Class IsPreord (A : Type) (HR : HasOrdRel A) : Prop := {
  is_refl :> IsRefl _<=_;
  is_trans :> IsTrans _<=_;
}.

Notation IsPreord := PreOrder.
