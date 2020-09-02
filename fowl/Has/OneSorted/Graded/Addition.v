From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Graded.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded addition.
    See [Has.OneSorted.Addition]. *)

Class HasGrdAdd {A : Type} (P : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_add : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdAdd.

Section Context.

Context {A : Type} {P : A -> Type} `{P_has_grd_add : HasGrdAdd A P}.

Global Instance P_has_grd_bin_op : HasGrdBinOp P := grd_add.

End Context.
