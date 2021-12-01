(** * Total Ordering *)

From DEZ.Has Require Export
  EquivalenceRelation OrderRelations.
From DEZ.Is Require Export
  PartialOrder Connex Reflexive.
From DEZ.ShouldHave Require Import
  EquivalenceNotations OrderRelationNotations.

(** ** Total Order *)

Class IsTotOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  is_part_ord :> IsPartOrd X Y;
  is_connex :> IsConnex Y;
}.

Section Context.

Context (A : Type) (X Y : A -> A -> Prop)
  `(!IsTotOrd X Y).

#[local] Instance has_eq_rel : HasEqRel A := X.
#[local] Instance has_ord_rel : HasOrdRel A := Y.

Ltac note := progress (
  try change X with _==_ in *;
  try change Y with _<=_ in *).

(** Total orders are reflexive. *)

#[local] Instance is_refl : IsRefl Y.
Proof.
  note.
  intros x.
  destruct (connex x x) as [l | l]; auto. Qed.

(** Total orders are transitive. *)

#[local] Instance is_trans : IsTrans Y.
Proof. typeclasses eauto. Qed.

(** Total orders are antisymmetric. *)

#[local] Instance is_antisym : IsAntisym X Y.
Proof. typeclasses eauto. Qed.

End Context.

#[export] Hint Resolve is_refl : typeclass_instances.
