From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Graded.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded negation.
    See [Has.OneSorted.Negation]. *)

Class HasGrdNeg {A : Type} (P : A -> Type)
  {A_has_un_op : HasUnOp A} : Type :=
  grd_neg : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdNeg.

Section Context.

Context {A : Type} {P : A -> Type} `{P_has_grd_neg : HasGrdNeg A P}.

Global Instance P_has_grd_bin_op : HasGrdUnOp P := grd_neg.

End Context.
