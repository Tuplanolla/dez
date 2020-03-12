From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsComm {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) : Prop :=
  comm : forall x y : A, x + y == y + x.

Class IsCommE {A : Type} (has_bin_op : HasBinOp A) : Prop :=
  commE : forall x y : A, x + y = y + x.
