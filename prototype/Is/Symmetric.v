From Maniunfold.Has Require Export
  Relation.

Class IsSymmetric {A : Type} (has_rel : HasRel A) : Prop :=
  symmetric : forall x y : A, x ~ y -> y ~ x.
