From Maniunfold.Has Require Export
  EquivalenceRelation Unit UnaryOperation.
From Maniunfold.Is Require Export
  ExternallyAbsorbing.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_un : HasUn A) (has_un_op : HasUnOp A) : Prop :=
  absorb : - 0 == 0.
