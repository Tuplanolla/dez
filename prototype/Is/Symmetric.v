From Coq Require Import
  RelationClasses.
From Maniunfold Require Export
  Init.
From Maniunfold.Has Require Export
  Relation.

Class IsSymmetric {A : Type} (has_rel : HasRel A) : Prop :=
  symmetric : forall x y : A, x ~ y -> y ~ x.

Section Context.

Context {A : Type} `{is_symmetric : IsSymmetric A}.

Global Instance symmetric_is_symmetric : Symmetric rel | 0 := symmetric.

End Context.
