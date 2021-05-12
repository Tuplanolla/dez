(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Class IsAsym (A : Type) `(HasBinRel A) : Prop :=
  asym : forall x y : A, x ~~ y -> ~ (y ~~ x).

Section Context.

Context (A : Type) `{IsAsym A}.

Global Instance bin_rel_asymmetric : Asymmetric bin_rel | 0.
Proof. intros x y. apply asym. Defined.

End Context.
