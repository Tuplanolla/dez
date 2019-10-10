From Maniunfold.Has Require Export
  Relation.

Class IsTransitive (A : Type) {has_rel : HasRel A} : Prop :=
  rel_transitive : forall x y z : A, x ~ y -> y ~ z -> x ~ z.
