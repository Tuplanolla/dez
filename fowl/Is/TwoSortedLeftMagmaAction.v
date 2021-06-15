(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation Action.
From Maniunfold.Is Require Export
  OneSortedMagma.

Class IsLMagAct (A B : Type)
  `(HasBinOp A) `(HasActL A B) : Prop := {
  A_bin_op_is_mag :> IsMag (bin_op (A := A));
}.
