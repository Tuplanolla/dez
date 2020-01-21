From Maniunfold.Has Require Export
  BinaryRelation LeftExternalBinaryOperation RightExternalBinaryOperation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsExtAssoc {A B C : Type} {has_bin_rel : HasBinRel C}
  (has_l_ext_bin_op : HasLExtBinOp A C)
  (has_r_ext_bin_op : HasRExtBinOp B C) : Prop :=
  ext_assoc : forall (x : A) (y : C) (z : B), x +< (y >+ z) ~~ (x +< y) >+ z.
