From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Graded.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Graded reciprocation.
    See [Has.OneSorted.Reciprocation]. *)

Class HasGrdRecip {A : Type} (P : A -> Type)
  {A_has_un_op : HasUnOp A} : Type :=
  grd_recip : forall i : A, P i -> P (- i).

Typeclasses Transparent HasGrdRecip.

Section Context.

Context {A : Type} {P : A -> Type} `{P_has_grd_recip : HasGrdRecip A P}.

Global Instance P_has_grd_un_op : HasGrdUnOp P := grd_recip.

End Context.
