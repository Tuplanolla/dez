From Maniunfold.Has Require Export
  EquivalenceRelation NullaryOperation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsUnAbsorb {A : Type}
  (has_null_op : HasNullOp A) (has_un_op : HasUnOp A) : Prop :=
  un_absorb : - 0 = 0.
