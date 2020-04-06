(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation TwoSorted.Graded.LeftAction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class HasGrdBinOp {A : Type} (P : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_bin_op : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdBinOp.

Section Context.

Context {A : Type} {P : A -> Type} `{A_has_grd_bin_op : HasGrdBinOp A P}.

Global Instance P_P_has_grd_l_act : HasGrdLAct P P := grd_bin_op.
(* Global Instance A_has_grd_r_act : HasGrdRAct A A := grd_bin_op.
Global Instance A_has_tor : HasTor A A := grd_bin_op. *)

End Context.
