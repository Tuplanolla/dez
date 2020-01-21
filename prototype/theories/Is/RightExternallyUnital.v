From Maniunfold.Has Require Export
  BinaryRelation RightExternalBinaryOperation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRExtUn {A B : Type} {has_bin_rel : HasBinRel B}
  (has_r_ext_bin_op : HasRExtBinOp A B) (has_un : HasUn A) : Prop :=
  r_ext_un : forall x : B, x >+ 0 ~~ x.
