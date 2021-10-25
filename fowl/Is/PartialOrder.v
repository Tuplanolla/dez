(** * Partial Ordering *)

From DEZ.Has Require Export
  EquivalenceRelation OrderRelations.
From DEZ.Is Require Export
  Preorder Antisymmetric Equivalence.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations OrderRelationNotations.

(** ** Partial Order *)
(** ** Poset *)

(** We cannot define [IsPartOrd] as a notation for [PartialOrder],
    because [PartialOrder] is constrained by [Equivalence] and
    built from [relation_equivalence]. *)

Fail Fail Notation IsPartOrd := PartialOrder.

Class IsPartOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  is_preord :> IsPreord Y;
  is_antisym :> IsAntisym X Y;
}.

(** These instances witness the compatibility of the definitions. *)

Section Context.

Context (A : Type) (X Y : A -> A -> Prop).

#[local] Instance has_eq_rel : HasEqRel A := X.
#[local] Instance has_ord_rel : HasOrdRel A := Y.

Ltac note := progress (
  try change X with _==_ in *;
  try change Y with _<=_ in *).

#[local] Instance is_part_ord `(!IsEq X)
  `(!IsPreord Y) `(!PartialOrder X Y) : IsPartOrd X Y.
Proof. split; typeclasses eauto. Qed.

#[local] Instance partial_order
  `(!IsEq X) `(!IsPartOrd X Y) : PartialOrder X Y.
Proof. Fail split; typeclasses eauto. Admitted.

End Context.

#[export] Hint Resolve is_part_ord : typeclass_instances.
