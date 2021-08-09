(** * Partial Order or Poset *)

From DEZ.Has Require Export
  OrderRelations.
From DEZ.Is Require Export
  Preorder Antisymmetric.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

(** We cannot define [IsPartOrd] as a notation for [PartialOrder _=_],
    because [PartialOrder] is built from [relation_equivalence]. *)

Fail Fail Notation IsPartOrd := (PartialOrder _=_).

Class IsPartOrd (A : Type) (HR : HasOrdRel A) : Prop := {
  is_preord :> IsPreord _<=_;
  is_antisym :> IsAntisym _<=_;
}.

Section Context.

Context (A : Type) (HR : HasOrdRel A)
  `(!IsPreord _<=_) `(!PartialOrder _=_ _<=_).

#[local] Instance partial_order : IsPartOrd _<=_.
Proof.
  split.
  - auto.
  - apply partial_order_antisym. auto. Qed.

End Context.

#[export] Hint Resolve partial_order : typeclass_instances.
