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

Class IsTwoGrdLLDistr {A : Type} (P Q : A -> Type)
  `{HasBinOp A} `{HasNullOp A}
  `(forall i : A, HasAdd (Q i))
  `(HasGrdLAct A P Q) : Prop :=
  grd_two_l_l_distr : forall {i j : A} (a : P i) (x y : Q j),
    a * (x + y) = a * x + a * y.
