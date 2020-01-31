From Maniunfold.Has Require Export
  EquivalenceRelation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsInj {A : Type} {has_eq_rel : HasEqRel A}
  (has_un_op : HasUnOp A) : Prop :=
  inj : forall x y : A, - x == - y -> x == y.
