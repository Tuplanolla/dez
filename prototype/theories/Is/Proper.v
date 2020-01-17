From Coq Require Export
  Morphisms.
From Maniunfold.Has Require Export
  BinaryRelation Point.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsProper {A : Type}
  (has_bi_rel : HasBinRel A) (has_pt : HasPt A) : Prop :=
  proper : pt ~ pt.

Section Context.

Context {A : Type} `{is_proper : IsProper A}.

Global Instance proper_is_proper : Proper bi_rel pt | 0 := proper.

End Context.
