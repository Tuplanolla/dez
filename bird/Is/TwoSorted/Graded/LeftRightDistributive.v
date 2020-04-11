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

Class IsTwoGrdLRDistr {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop :=
  grd_two_l_r_distr : forall {i j : A} (a b : P i) (x : Q j),
    (a + b) * x = a * x + b * x.
