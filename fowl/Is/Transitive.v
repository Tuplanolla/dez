(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSorted.BinaryRelationNotations.

Class IsTrans (A : Type) (A_has_bin_rel : HasBinRel A) : Prop :=
  trans : forall x y z : A, x ~~ y -> y ~~ z -> x ~~ z.

Section Context.

Context {A : Type} `{is_trans : IsTrans A}.

Global Instance bin_rel_transitive : Transitive bin_rel | 0.
Proof. intros x y z. apply trans. Defined.

End Context.
