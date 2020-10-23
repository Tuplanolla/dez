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
  `{HasBinOp A} `{HasUnOp A}
  `{!@HasGrdAdd A P bin_op} `{!@HasGrdNeg A P un_op}.

(** Graded subtraction.
    See [Offers.OneSorted.Arithmetic]. *)

Definition grd_sub (i j : A) (x : P i) (y : P j) : P (i - j)%ring :=
  (x + (- y))%grd_ring.

End Context.

Section Context.

Context {A : Type} {P : A -> Type}
  `{HasBinOp A} `{HasUnOp A}
  `{!@HasGrdMul A P bin_op} `{!@HasGrdRecip A P un_op}.

(** Graded division.
    See [Offers.OneSorted.Arithmetic]. *)

Definition grd_div (i j : A) (x : P i) (y : P j) : P (i - j)%ring :=
  (x * (/ y))%grd_ring.

End Context.
