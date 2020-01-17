From Maniunfold.Has Require Export
  EquivalenceRelation LeftExternalBinaryOperation RightExternalBinaryOperation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsExternallyAssociative {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_l_ex_bin_op : HasLExBinOp A C)
  (has_r_ex_bin_op : HasRExBinOp B C) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  externally_associative : forall (x : A) (y : C) (z : B),
    x +< (y >+ z) == (x +< y) >+ z;
}.
