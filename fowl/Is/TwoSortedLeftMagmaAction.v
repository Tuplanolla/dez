(* bad *)
From DEZ.Has Require Export
  BinaryOperation Action.
From DEZ.Is Require Export
  Magma.

Class IsLMagAct (A B : Type)
  `(HasBinOp A) `(HasActL A B) : Prop := {
  A_bin_op_is_mag :> IsMag eq (bin_op (A := A));
}.
