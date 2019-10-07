From Maniunfold.Has Require Import Relation.

Class IsTransitive (A : Type) {has_rel : HasRel A} : Prop :=
  rel_transitive : forall x y z : A, x ~ y -> y ~ z -> x ~ z.
