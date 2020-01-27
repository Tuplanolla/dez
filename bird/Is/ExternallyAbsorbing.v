From Maniunfold.Has Require Export
  BinaryRelation Unit Function.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsExtAbsorb {A B : Type} {has_bin_rel : HasBinRel B}
  (A_has_un : HasUn A) (B_has_un : HasUn B) (has_fn : HasFn A B) : Prop :=
  ext_absorb : >-< 0 ~~ 0.
