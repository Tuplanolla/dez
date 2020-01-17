From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsSymmetric {A : Type} (has_bi_rel : HasBinRel A) : Prop :=
  symmetric : forall x y : A, x ~ y -> y ~ x.

Section Context.

Context {A : Type} `{is_symmetric : IsSymmetric A}.

Global Instance bi_rel_symmetric : Symmetric bi_rel | 0 := symmetric.

End Context.
