From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.UnaryOperation
  OneSorted.Graded.Addition OneSorted.Graded.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.Reciprocation.
From Maniunfold.ShouldHave Require Import
  OneSorted.Graded.ArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  OneSorted.ArithmeticNotations.

Section Context.

Context {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_un_op : HasUnOp A}
  {P_has_grd_add : HasGrdAdd P} {P_has_grd_neg : HasGrdNeg P}.

(** Graded subtraction.
    See [Offers.OneSorted.Arithmetic]. *)

Definition grd_sub (i j : A) (x : P i) (y : P j) : P (i - j)%ring :=
  (x + (- y))%grd_ring.

End Context.

Section Context.

Context {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_un_op : HasUnOp A}
  {P_has_grd_mul : HasGrdMul P} {P_has_grd_recip : HasGrdRecip P}.

(** Graded division.
    See [Offers.OneSorted.Arithmetic]. *)

Definition grd_div (i j : A) (x : P i) (y : P j) : P (i - j)%ring :=
  (x * (/ y))%grd_ring.

End Context.
