(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Magma.

Class IsLMagAct (A B : Type)
  `(HasBinOp A) `(HasLAct A B) : Prop := {
  A_bin_op_is_mag :> IsMag (bin_op (A := A));
}.
