From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  Semigroup OneSortedly.Unital.

Class IsMon {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_is_sgrp :> IsSgrp bin_op;
  bin_op_un_is_unl :> IsUnl bin_op un;
}.

Class IsMonE {A : Type} (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_is_sgrpE :> IsSgrpE bin_op;
  bin_op_un_is_unlE :> IsUnlE bin_op un;
}.
