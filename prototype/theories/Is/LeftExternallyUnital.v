From Maniunfold.Has Require Export
  EquivalenceRelation LeftExternalBinaryOperation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftExternallyUnital {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_ex_bin_op : HasLExBinOp A B) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_externally_unital : forall x : B, 0 +< x == x;
}.
