From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded multiplication.
    See [Has.OneSorted.Multiplication]. *)

Class HasGrdMul {A : Type} (P : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_mul : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdMul.

Section Context.

Context {A : Type} {P : A -> Type} `{P_has_grd_mul : HasGrdMul A P}.

Global Instance P_has_grd_bin_op : HasGrdBinOp P := grd_mul.

End Context.
