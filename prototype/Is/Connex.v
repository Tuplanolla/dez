From Maniunfold.Has Require Export
  Relation.

Class IsConnex {A : Type} (has_rel : HasRel A) : Prop :=
  connex : forall x y : A, x ~ y \/ y ~ x.
