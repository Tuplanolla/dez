(** * Total Order *)

From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.Is Require Export
  Preorder PartialOrder Connex Reflexive.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsTotOrd (A : Type) (HR : HasOrdRel A) : Prop := {
  is_part_ord :> IsPartOrd _<=_;
  is_connex :> IsConnex _<=_;
}.

Section Context.

Context (A : Type) (HR : HasOrdRel A) `(!IsTotOrd _<=_).

Import OrderRelations.Subclass.

Ltac conversions := typeclasses
  convert bin_rel into ord_rel.

(** Total orders are reflexive. *)

#[local] Instance is_refl : IsRefl _<=_.
Proof with conversions.
  intros x.
  destruct (connex x x) as [l | l]...
  - apply l.
  - apply l. Qed.

End Context.

#[export] Hint Resolve is_refl : typeclass_instances.
