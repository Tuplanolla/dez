(** * Total Order *)

From DEZ Require Export
  TypeclassTactics.
From DEZ.Has Require Export
  OrderRelations.
From DEZ.Is Require Export
  Preorder PartialOrder Connex Reflexive.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

Class IsTotOrd (A : Type) (HR : HasOrdRel A) : Prop := {
  is_part_ord :> IsPartOrd _<=_;
  is_connex :> IsConnex _<=_;
}.

Section Context.

Context (A : Type) (HR : HasOrdRel A) `(!IsTotOrd _<=_).

Import OrderRelations.Subclass.

Ltac subclass := progress (
  try change bin_rel with ord_rel in *).

(** Total orders are reflexive. *)

#[local] Instance is_refl : IsRefl _<=_.
Proof with subclass.
  intros x.
  destruct (connex x x) as [l | l].
  - apply l.
  - apply l. Qed.

End Context.

#[export] Hint Resolve is_refl : typeclass_instances.
