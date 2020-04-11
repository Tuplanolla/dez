(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.Function.
From Maniunfold.Has Require Export
  TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.UnaryDistributive TwoSorted.RightBinaryCommutative
  TwoSorted.LeftModule.
From Maniunfold.Is Require Export
  OneSorted.UnaryDistributive TwoSorted.RightBinaryCommutative
  TwoSorted.RightModule.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRHomogen (A B C : Type)
  (A_B_has_r_act : HasRAct A B) (A_C_has_r_act : HasRAct A C)
  (B_C_has_fn : HasFn B C) : Prop :=
  r_homogen : forall (a : A) (x : B), fn (x * a) = fn x * a.
