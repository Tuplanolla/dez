From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation RightAction.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRCompat {A B : Type}
  (has_bin_op : HasBinOp A) (has_r_act : HasRAct A B) : Prop :=
  r_compat : forall (a b : A) (x : B), x R+ (a + b) = (x R+ a) R+ b.
