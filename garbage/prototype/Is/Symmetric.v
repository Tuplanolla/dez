From Coq Require Export
  Setoid.
From DEZ.Has Require Export
  Relation.
From DEZ.ShouldHave Require Import
  RelationNotations.

Class IsSymmetric {A : Type} (has_rel : HasRel A) : Prop :=
  symmetric : forall x y : A, x ~ y -> y ~ x.

Section Context.

Context {A : Type} `{is_symmetric : IsSymmetric A}.

Global Instance rel_symmetric : Symmetric rel | 0 := symmetric.

Theorem symmetric_iff : forall x y : A, x ~ y <-> y ~ x.
Proof. intros x y. split; auto. Qed.

End Context.
