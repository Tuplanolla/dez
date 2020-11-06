(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSorted.BinaryRelationNotations.

Class IsTrans (A : Type) `(HasBinRel A) : Prop :=
  trans : forall x y z : A, x ~~ y -> y ~~ z -> x ~~ z.

Section Context.

Context (A : Type) `(IsTrans A).

Global Instance bin_rel_transitive : Transitive bin_rel | 0.
Proof. intros x y z. apply trans. Defined.

End Context.
