From Coq Require Import
  RelationClasses.
From Maniunfold Require Export
  Init.
From Maniunfold.Has Require Export
  Relation.

Class IsTransitive {A : Type} (has_rel : HasRel A) : Prop :=
  transitive : forall x y z : A, x ~ y -> y ~ z -> x ~ z.

Section Context.

Context {A : Type} `{is_transitive : IsTransitive A}.

Global Instance transitive_is_transitive : Transitive rel | 0 := transitive.

End Context.
