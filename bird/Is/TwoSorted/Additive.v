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

Class IsAddve (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_fn : HasFn A B) : Prop :=
  addve : forall x y : A, fn (x + y) = fn x + fn y.
