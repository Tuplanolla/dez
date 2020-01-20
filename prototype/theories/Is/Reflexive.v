From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsRefl {A : Type} (has_bin_rel : HasBinRel A) : Prop :=
  reflexive : forall x : A, x ~ x.

Section Context.

Context {A : Type} `{is_reflexive : IsRefl A}.

Global Instance bin_rel_reflexive : Reflexive bin_rel | 0 := reflexive.

End Context.
