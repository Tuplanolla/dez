From Maniunfold.Has Require Export
  EquivalenceRelation Relation.
From Maniunfold.Is Require Export
  Setoid.

Class IsAntisymmetric {A : Type} {has_eqv : HasEqv A}
  (has_rel : HasRel A) : Prop := {
  eqv_is_setoid :> IsSetoid A;
  rel_antisymmetric : forall x y : A, x ~ y -> y ~ x -> x == y;
}.
