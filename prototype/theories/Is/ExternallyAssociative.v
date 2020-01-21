From Maniunfold.Has Require Export
  EquivalenceRelation LeftExternalBinaryOperation RightExternalBinaryOperation.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsExtAssoc {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_l_ext_bin_op : HasLExtBinOp A C)
  (has_r_ext_bin_op : HasRExtBinOp B C) : Prop :=
  ext_assoc : forall (x : A) (y : C) (z : B), x +< (y >+ z) == (x +< y) >+ z.
