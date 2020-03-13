From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation LeftAction.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLCompat {A B : Type}
  (has_bin_op : HasBinOp A) (has_l_act : HasLAct A B) : Prop :=
  l_compat : forall (a b : A) (x : B), a L+ (b L+ x) = (a + b) L+ x.
