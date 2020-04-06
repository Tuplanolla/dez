(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsAsym {A : Type} (A_has_bin_rel : HasBinRel A) : Prop :=
  asym : forall x y : A, x ~~ y -> ~ (y ~~ x).

Section Context.

Context {A : Type} `{is_asym : IsAsym A}.

Global Instance bin_rel_asymmetric : Asymmetric bin_rel | 0.
Proof. intros x y. apply asym. Qed.

End Context.
