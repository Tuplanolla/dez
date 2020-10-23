(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.LeftUnital.
From Maniunfold.ShouldHave Require Import
  OneSorted.Graded.AdditiveNotations.

Class IsGrdLUnl {A : Type} (P : A -> Type)
  `{HasBinOp A} `{HasNullOp A}
  `(HasGrdBinOp A P)
  `(HasGrdNullOp A P) : Prop := {
  A_bin_op_null_op_is_l_unl :> IsLUnl A bin_op null_op;
  grd_l_unl : forall {i : A} (x : P i), rew l_unl i in (0 + x) = x;
}.
