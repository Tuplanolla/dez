From Maniunfold.Has Require Export
  EquivalenceRelation RightExternalBinaryOperation.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRExtUn {A B : Type} {has_eq_rel : HasEqRel B}
  (has_r_ext_bin_op : HasRExtBinOp A B) (has_un : HasUn A) : Prop :=
  r_ext_un : forall x : B, x >+ 0 == x.
