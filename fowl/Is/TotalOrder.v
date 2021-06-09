(** * Total Order *)

From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  OrderRelation.
From Maniunfold.Is Require Export
  Preorder PartialOrder Connex Reflexive.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

(** We need to include [IsPreord] in [IsTotOrd],
    because the definition under [IsPartOrd] is a bit wonky. *)

Class IsTotOrd (A : Type) (R : HasOrdRel A) : Prop := {
  is_preord :> IsPreord _<=_;
  is_part_ord :> IsPartOrd _<=_;
  is_connex :> IsConnex _<=_;
}.

Section Context.

Context (A : Type) (R : HasOrdRel A) `(!IsTotOrd _<=_).

Ltac conversions := typeclasses
  convert bin_rel into ord_rel.

#[local] Instance is_refl : IsRefl _<=_.
Proof with conversions.
  intros x.
  destruct (connex x x) as [l | l]...
  - apply l.
  - apply l. Qed.

End Context.

#[export] Hint Resolve is_refl : typeclass_instances.
