(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  Graded.BinaryOperation Graded.NullaryOperation TwoSorted.Graded.LeftAction.
From Maniunfold.Is Require Export
  Graded.Ring AbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations
  TwoSorted.Graded.MultiplicativeNotations.

Local Open Scope grd_l_mod_scope.

Class IsTwoGrdLUnl (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasGrdLAct A P Q)
  `(HasGrdOne A P) : Prop := {
  A_bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  grd_two_l_unl : forall {i : A} (x : Q i),
    rew l_unl i in (1 * x) = x;
}.
