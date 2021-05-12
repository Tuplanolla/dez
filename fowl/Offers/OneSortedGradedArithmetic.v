From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedUnaryOperation
  OneSortedGradedAddition OneSortedGradedNegation
  OneSortedGradedMultiplication OneSortedGradedReciprocation.
From Maniunfold.ShouldHave Require Import
  OneSortedGradedArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  OneSortedArithmeticNotations.

Section Context.

Context (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasUnOp A) `(!HasGrdAdd P bin_op) `(!HasGrdNeg P un_op).

(** Graded subtraction.
    See [Offers.OneSortedArithmetic]. *)

Definition grd_sub (i j : A) (x : P i) (y : P j) : P (i - j)%ring :=
  (x + (- y))%grd_ring.

End Context.

Section Context.

Context (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasUnOp A) `(!HasGrdMul P bin_op) `(!HasGrdRecip P un_op).

(** Graded division.
    See [Offers.OneSortedArithmetic]. *)

Definition grd_div (i j : A) (x : P i) (y : P j) : P (i - j)%ring :=
  (x * (/ y))%grd_ring.

End Context.
