From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsSym {A : Type} (has_bin_rel : HasBinRel A) : Prop :=
  symmetric : forall x y : A, x ~ y -> y ~ x.

Section Context.

Context {A : Type} `{is_symmetric : IsSym A}.

Global Instance bin_rel_symmetric : Symmetric bin_rel | 0 := symmetric.

End Context.
