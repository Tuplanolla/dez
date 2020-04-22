From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  Relation.
From Maniunfold.ShouldHave Require Import
  RelationNotations.

Class IsTransitive {A : Type} (has_rel : HasRel A) : Prop :=
  transitive : forall x y z : A, x ~ y -> y ~ z -> x ~ z.

Section Context.

Context {A : Type} `{is_transitive : IsTransitive A}.

Global Instance rel_transitive : Transitive rel | 0 := transitive.

End Context.
