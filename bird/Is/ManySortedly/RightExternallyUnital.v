From Maniunfold.Has Require Export
  BinaryRelation RightExternalBinaryOperation RightUnit.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRExtUnl {A B : Type} {has_bin_rel : HasBinRel B}
  (has_r_ext_bin_op : HasRExtBinOp A B) (has_r_un : HasRUn A) : Prop :=
  r_ext_unl : forall x : B, x R+ R0 ~~ x.
