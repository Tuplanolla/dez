From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation OneSorted.BinaryRelation.
From Maniunfold.Is Require Export
  OneSortedly.Equivalence Proper.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations EquivalenceRelationNotations.

Class IsAntisym {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_rel : HasBinRel A) : Prop := {
  eq_rel_is_eq :> IsEq eq_rel;
  bin_rel_is_proper :> IsProper (eq_rel ==> eq_rel ==> flip impl) bin_rel;
  antisym : forall x y : A, x ~~ y -> y ~~ x -> x == y;
}.

Section Context.

Context {A : Type} `{is_antisym : IsAntisym A}.

Global Instance bin_rel_antisymmetric : Antisymmetric A eq_rel bin_rel | 0.
Proof. intros x y. apply antisym. Qed.

End Context.
