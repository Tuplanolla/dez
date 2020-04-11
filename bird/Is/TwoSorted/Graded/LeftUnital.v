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

Class IsTwoGrdLUnl {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_one : HasGrdOne P)
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  grd_two_l_unl : forall {i : A} (x : Q i),
    rew l_unl i in (1 * x) = x;
}.
