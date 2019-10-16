From Maniunfold.Has Require Export
  Relation.

Class IsTransitive {A : Type} (has_rel : HasRel A) : Prop :=
  transitive : forall x y z : A, x ~ y -> y ~ z -> x ~ z.
