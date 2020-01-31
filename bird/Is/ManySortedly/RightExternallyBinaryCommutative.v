From Maniunfold.Has Require Export
  BinaryRelation LeftExternalBinaryOperation RightUnaryOperation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRExtBinComm {A B : Type} {has_bin_rel : HasBinRel B}
  (has_l_ext_bin_op : HasLExtBinOp A B) (has_r_un_op : HasRUnOp B) : Prop :=
  r_ext_bin_comm : forall (x : A) (y : B), R- (x L+ y) ~~ x L+ R- y.
