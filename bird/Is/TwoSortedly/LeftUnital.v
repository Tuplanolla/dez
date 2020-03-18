From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation LeftAction LeftNullaryOperation.
From Maniunfold.ShouldHave Require Import
  TwoSorted.AdditiveNotations.

Class IsTwoLUnl {A B : Type}
  (has_l_null_op : HasLNullOp A) (has_l_act : HasLAct A B) : Prop :=
  two_l_unl : forall x : B, L0 L+ x = x.
