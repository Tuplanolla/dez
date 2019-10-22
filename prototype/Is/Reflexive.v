From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  Relation.
From Maniunfold.Supports Require Import
  RelationNotations.

Class IsReflexive {A : Type} (has_rel : HasRel A) : Prop :=
  reflexive : forall x : A, x ~ x.

Section Context.

Context {A : Type} `{is_reflexive : IsReflexive A}.

Global Instance rel_reflexive : Reflexive rel | 0 := reflexive.

End Context.
