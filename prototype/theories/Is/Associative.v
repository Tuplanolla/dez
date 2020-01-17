From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Setoid ExternallyAssociative.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsAssociative {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBiOp A) : Prop := {
  bi_op_is_externally_associative :> IsExternallyAssociative bi_op (flip bi_op);
}.
