From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsUnaryDistributive {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  un_distr : forall x y : A, - (x + y) == - x + - y.
