From Maniunfold.Has Require Export
  BinaryOperation Unit.
From Maniunfold.Is Require Export
  OneSortedly.Semigroup OneSortedly.Unital.

Class IsMon {A : Type} (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_is_sgrp :> IsSgrp bin_op;
  bin_op_un_is_unl :> IsUnl bin_op un;
}.
