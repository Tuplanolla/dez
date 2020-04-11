(* bad *)
From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation OneSorted.OrderRelation.
From Maniunfold.Is Require Export
  Antisymmetric Connex Transitive Reflexive
  OneSorted.PartialOrder.
From Maniunfold.ShouldHave Require Import
  OneSorted.OrderRelationNotations.

Class IsTotOrd (A : Type)
  (A_has_ord_rel : HasOrdRel A) : Prop := {
  A_ord_is_antisym :> IsAntisym A ord_rel;
  A_ord_is_connex :> IsConnex A ord_rel;
  A_ord_is_trans :> IsTrans A ord_rel;
}.

Section Context.

Context {A : Type} `{is_tot_ord : IsTotOrd A}.

Ltac conversions := typeclasses
  convert bin_rel into ord_rel.

Theorem A_ord_rel_refl : forall x : A,
  x <= x.
Proof with conversions.
  intros x. destruct (connex x x) as [H | H]...
  - apply H.
  - apply H. Defined.

Global Instance A_ord_rel_is_refl : IsRefl A ord_rel.
Proof. intros x. apply A_ord_rel_refl. Defined.

Global Instance A_ord_rel_is_part_ord : IsPartOrd A ord_rel.
Proof. repeat (split; try typeclasses eauto). Defined.

End Context.
