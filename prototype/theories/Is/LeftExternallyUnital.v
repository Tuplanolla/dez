From Maniunfold.Has Require Export
  BinaryRelation LeftExternalBinaryOperation Unit.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLExtUn {A B : Type} {has_bin_rel : HasBinRel B}
  (has_l_ext_bin_op : HasLExtBinOp A B) (has_un : HasUn A) : Prop :=
  l_ext_un : forall x : B, 0 +< x ~~ x.
