(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation GradedBinaryOperation.
From Maniunfold.Is Require Export
  Magma.

Class IsGrdMag (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_mag :> IsMag (bin_op (A := A));
}.
