(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class HasGrdRAct {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_r_act : forall i j : A, Q i -> P j -> Q (i + j).

Typeclasses Transparent HasGrdRAct.
