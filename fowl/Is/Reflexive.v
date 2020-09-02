(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsRefl (A : Type) (A_has_bin_rel : HasBinRel A) : Prop :=
  refl : forall x : A, x ~~ x.

Section Context.

Context {A : Type} `{is_refl : IsRefl A}.

Global Instance bin_rel_reflexive : Reflexive bin_rel | 0.
Proof. intros x. apply refl. Defined.

End Context.
