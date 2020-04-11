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

Local Open Scope l_mod_scope.

Class IsLHomogen (A B C : Type)
  (A_B_has_l_act : HasLAct A B) (A_C_has_l_act : HasLAct A C)
  (B_C_has_fn : HasFn B C) : Prop :=
  l_homogen : forall (a : A) (x : B), fn (a * x) = a * fn x.
