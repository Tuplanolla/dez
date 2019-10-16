From Maniunfold.Has Require Export
  Relation.

Class IsReflexive {A : Type} (has_rel : HasRel A) : Prop :=
  reflexive : forall x : A, x ~ x.
