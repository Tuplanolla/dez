From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation RightAction RightNullaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsTwoRUnl {A B : Type}
  (has_r_null_op : HasRNullOp A) (has_r_act : HasRAct A B) : Prop :=
  two_r_unl : forall x : B, x R+ R0 = x.
