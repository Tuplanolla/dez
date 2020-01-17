From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsAssociative {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBinOp A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  associative : forall x y z : A,
    x + (y + z) == (x + y) + z;
}.
