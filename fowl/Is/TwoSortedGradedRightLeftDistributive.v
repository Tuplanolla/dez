(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation
  OneSortedGradedBinaryOperation OneSortedGradedNullaryOperation
  TwoSortedGradedLeftAction.
From Maniunfold.Is Require Export
  OneSortedGradedRing OneSortedAbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedAdditiveNotations
  OneSortedGradedMultiplicativeNotations
  TwoSortedGradedMultiplicativeNotations.

(** TODO Check ungraded argument order to be consistent. *)

Local Open Scope grd_r_mod_scope.

Class IsTwoGrdRLDistr (A : Type) (P Q : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(forall i : A, HasAdd (P i))
  `(forall i : A, HasAdd (Q i))
  `(!HasGrdRAct P Q bin_op) : Prop :=
  grd_two_r_l_distr : forall (i j : A) (x : Q i) (a b : P j),
    x * (a + b) = x * a + x * b.
