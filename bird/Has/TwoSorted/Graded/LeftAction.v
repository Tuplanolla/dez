From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class HasGrdLAct {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_l_act : forall i j : A, P i -> Q j -> Q (i + j).

Typeclasses Transparent HasGrdLAct.
