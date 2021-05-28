(* bad *)
From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  OneSortedEquivalenceRelation OneSortedOrderRelation.
From Maniunfold.Is Require Export
  Antisymmetric Connex Transitive Reflexive
  OneSortedPartialOrder.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Class IsTotOrd (A : Type)
  `(HasOrdRel A) : Prop := {
  A_ord_is_antisym :> IsAntisym ord_rel;
  A_ord_is_connex :> IsConnex ord_rel;
  A_ord_is_trans :> IsTrans ord_rel;
}.

Section Context.

Context (A : Type) `{IsTotOrd A}.

Ltac conversions := typeclasses
  convert bin_rel into ord_rel.

Theorem A_ord_rel_refl : forall x : A,
  x <= x.
Proof with conversions.
  intros x. destruct (connex x x) as [Hyp | Hyp]...
  - apply Hyp.
  - apply Hyp. Defined.

Global Instance A_ord_rel_is_refl : IsRefl ord_rel.
Proof. intros x. apply A_ord_rel_refl. Defined.

Global Instance A_ord_rel_is_part_ord : IsPartOrd ord_rel.
Proof. repeat (split; try typeclasses eauto). Defined.

End Context.
