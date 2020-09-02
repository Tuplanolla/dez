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

(** TODO Check ungraded argument order to be consistent. *)

Local Open Scope grd_r_mod_scope.

Class IsTwoGrdRLDistr {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop :=
  grd_two_r_l_distr : forall {i j : A} (x : Q i) (a b : P j),
    x * (a + b) = x * a + x * b.
