From Maniunfold.Has Require Import Relation.

Class IsConnex (A : Type) {has_rel : HasRel A} : Prop :=
  rel_connex : forall x y : A, x ~ y \/ y ~ x.
