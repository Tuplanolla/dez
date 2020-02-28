From Maniunfold.Has Require Export
  BinaryRelation LeftAction LeftUnit.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLExtUnl {A B : Type} {has_bin_rel : HasBinRel B}
  (has_l_act : HasLAct A B) (has_l_un : HasLUn A) : Prop :=
  l_ext_unl : forall x : B, L0 L+ x ~~ x.
