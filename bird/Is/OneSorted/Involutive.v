(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsInvol {A : Type} (A_has_un_op : HasUnOp A) : Prop :=
  invol : forall x : A, - (- x) = x.
