From Maniunfold.Has Require Export
  OneSorted.BinaryRelation RightAction RightUnit.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRExtUnl {A B : Type} {has_bin_rel : HasBinRel B}
  (has_r_act : HasRAct A B) (has_r_un : HasRUn A) : Prop :=
  r_ext_unl : forall x : B, x R+ R0 ~~ x.
