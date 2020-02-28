From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsSym {A : Type} (has_bin_rel : HasBinRel A) : Prop :=
  sym : forall x y : A, x ~~ y -> y ~~ x.

Section Context.

Context {A : Type} `{is_sym : IsSym A}.

Global Instance bin_rel_symmetric : Symmetric bin_rel | 0.
Proof. intros x y. apply sym. Qed.

End Context.
