From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsTransitive {A : Type} (has_bi_rel : HasBinRel A) : Prop :=
  transitive : forall x y z : A, x ~ y -> y ~ z -> x ~ z.

Section Context.

Context {A : Type} `{is_transitive : IsTransitive A}.

Global Instance bi_rel_transitive : Transitive bi_rel | 0 := transitive.

End Context.
