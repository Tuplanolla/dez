From Maniunfold.Has Require Export
  EquivalenceRelation LeftExternalBinaryOperation Unit.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLExtUn {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_ext_bin_op : HasLExtBinOp A B) (has_un : HasUn A) : Prop :=
  l_ext_un : forall x : B, 0 +< x == x.
