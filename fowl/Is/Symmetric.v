(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsSym (A : Type) `(HasBinRel A) : Prop :=
  sym : forall x y : A, x ~~ y -> y ~~ x.

Section Context.

Context (A : Type) `(IsSym A).

Global Instance bin_rel_symmetric : Symmetric bin_rel | 0.
Proof. intros x y. apply sym. Defined.

End Context.
