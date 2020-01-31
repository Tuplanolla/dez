From Maniunfold.Has Require Export
  EquivalenceRelation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsInvol {A : Type} {has_eq_rel : HasEqRel A}
  (has_un_op : HasUnOp A) : Prop :=
  invol : forall x : A, - - x == x.
