From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsReflexive {A : Type} (has_bi_rel : HasBinRel A) : Prop :=
  reflexive : forall x : A, x ~ x.

Section Context.

Context {A : Type} `{is_reflexive : IsReflexive A}.

Global Instance bi_rel_reflexive : Reflexive bi_rel | 0 := reflexive.

End Context.
