(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsIrrefl (A : Type) (A_has_bin_rel : HasBinRel A) : Prop :=
  irrefl : forall x : A, ~ (x ~~ x).

Section Context.

Context {A : Type} `{is_irrefl : IsIrrefl A}.

Global Instance bin_rel_reflexive : Irreflexive bin_rel | 0.
Proof. intros x. apply irrefl. Defined.

End Context.
