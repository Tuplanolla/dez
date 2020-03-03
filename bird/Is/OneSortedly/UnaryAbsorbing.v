From Maniunfold.Has Require Export
  EquivalenceRelation Unit UnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsUnAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_un : HasUn A) (has_un_op : HasUnOp A) : Prop :=
  un_absorb : - 0 == 0.
