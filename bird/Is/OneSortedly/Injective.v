From Maniunfold.Has Require Export
  EquivalenceRelation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsInj {A : Type}
  (has_un_op : HasUnOp A) : Prop :=
  inj : forall x y : A, - x = - y -> x = y.
