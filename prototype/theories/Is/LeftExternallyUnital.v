From Maniunfold.Has Require Export
  EquivalenceRelation LeftExternalBinaryOperation.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLExtUn {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_ext_bin_op : HasLExtBinOp A B) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsEq eq_rel;
  left_externally_unital : forall x : B, 0 +< x == x;
}.
