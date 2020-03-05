From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation OneSorted.OrderRelation.
From Maniunfold.Is Require Export
  OneSortedly.Preorder Antisymmetric.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations OrderRelationNotations.

Class IsPartOrd {A : Type} {has_eq_rel : HasEqRel A}
  (has_ord_rel : HasOrdRel A) : Prop := {
  ord_rel_is_antisym :> IsAntisym ord_rel;
  ord_rel_is_preord :> IsPreord ord_rel;
}.

Ltac change_part_ord :=
  change bin_rel with ord_rel in *.

Section Context.

Context {A : Type} `{is_part_ord : IsPartOrd A}.

Theorem ord_rel_partial_order' : forall x y : A,
  x == y <-> x <= y /\ y <= x.
Proof with change_part_ord.
  intros x y. split.
  - intros Hxy. split.
    + rewrite Hxy. reflexivity.
    + rewrite Hxy. reflexivity.
  - intros [Hxy Hyx]. apply antisym...
    + apply Hxy.
    + apply Hyx. Qed.

Global Instance ord_rel_partial_order : PartialOrder eq_rel ord_rel | 0.
Proof. intros x y. apply ord_rel_partial_order'. Qed.

End Context.
