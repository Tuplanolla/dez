From DEZ.Has Require Export
  Relation.
From DEZ.ShouldHave Require Import
  RelationNotations.

Class IsConnex {A : Type} (has_rel : HasRel A) : Prop :=
  connex : forall x y : A, x ~ y \/ y ~ x.
