(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Class IsIrrefl (A : Type) `(HasBinRel A) : Prop :=
  irrefl : forall x : A, ~ (x ~~ x).

Section Context.

Context (A : Type) `{IsIrrefl A}.

Global Instance bin_rel_reflexive : Irreflexive bin_rel | 0.
Proof. intros x. apply irrefl. Defined.

End Context.
