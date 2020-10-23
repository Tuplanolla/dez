(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.Is Require Export
  OneSorted.Magma.

Class IsGrdMag {A : Type} (P : A -> Type)
  `{HasBinOp A} `(HasGrdBinOp A P) : Prop := {
  A_bin_op_is_mag :> IsMag A bin_op;
}.
