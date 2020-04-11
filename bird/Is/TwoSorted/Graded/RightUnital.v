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

Local Open Scope grd_r_mod_scope.

Class IsTwoGrdRUnl {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_Q_has_grd_r_act : HasGrdRAct P Q)
  (P_has_grd_one : HasGrdOne P) : Prop := {
  A_bin_op_null_op_is_r_unl :> IsRUnl A bin_op null_op;
  grd_two_r_unl : forall {i : A} (x : Q i),
    rew r_unl i in (x * 1) = x;
}.
