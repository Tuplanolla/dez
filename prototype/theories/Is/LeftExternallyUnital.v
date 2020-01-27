From Maniunfold.Has Require Export
  BinaryRelation LeftExternalBinaryOperation LeftUnit.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLExtUnl {A B : Type} {has_bin_rel : HasBinRel B}
  (has_l_ext_bin_op : HasLExtBinOp A B) (has_l_un : HasLUn A) : Prop :=
  l_ext_unl : forall x : B, l_un +< x ~~ x.
