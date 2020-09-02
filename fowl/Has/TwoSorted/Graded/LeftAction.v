From Maniunfold.Has Require Export
  OneSorted.BinaryOperation ThreeSorted.Graded.BinaryFunction.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded action; left chirality.
    See [Has.OneSorted.LeftAction]. *)

Class HasGrdLAct {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} : Type :=
  grd_l_act : forall i j : A, P i -> Q j -> Q (i + j).

Typeclasses Transparent HasGrdLAct.

Section Context.

Context {A : Type} {P Q : A -> Type} `{P_Q_has_grd_l_act : HasGrdLAct A P Q}.

Global Instance P_Q_Q_has_grd_bin_fn : HasGrdBinFn P Q Q := grd_l_act.

End Context.
