From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation OneSorted.BinaryRelation.
From Maniunfold.Is Require Export
  OneSortedly.Equivalence.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations EquivalenceRelationNotations.

Class IsAntisym {A : Type} (has_bin_rel : HasBinRel A) : Prop :=
  antisym : forall x y : A, x ~~ y -> y ~~ x -> x = y.

Section Context.

Context {A : Type} `{is_antisym : IsAntisym A}.

Global Instance bin_rel_antisymmetric : Antisymmetric A eq bin_rel | 0.
Proof. intros x y. apply antisym. Qed.

End Context.
