From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation RightAction LeftUnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLExtBinComm {A B : Type}
  (has_l_un_op : HasLUnOp B) (has_r_act : HasRAct A B) : Prop :=
  l_ext_bin_comm : forall (x : B) (y : A), L- (x R+ y) = L- x R+ y.
