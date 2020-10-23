(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction ThreeSorted.BinaryFunction.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLBihomogen (A B C D : Type)
  `(HasLAct A B) `(HasLAct A D)
  `(HasBinFn B C D) : Prop :=
  l_bihomogen : forall (a : A) (x : B) (y : C),
    a * bin_fn x y = bin_fn (a * x) y.
