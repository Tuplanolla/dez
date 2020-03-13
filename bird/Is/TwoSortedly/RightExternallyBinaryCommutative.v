From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation LeftAction RightUnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRExtBinComm {A B : Type}
  (has_r_un_op : HasRUnOp B) (has_l_act : HasLAct A B) : Prop :=
  r_ext_bin_comm : forall (x : A) (y : B), R- (x L+ y) = x L+ R- y.
