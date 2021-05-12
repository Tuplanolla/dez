(* bad *)
From Maniunfold.Has Require Export
  TwoSortedLeftAction ThreeSortedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLBihomogen (A B C D : Type)
  `(HasLAct A B) `(HasLAct A D)
  `(HasBinFn B C D) : Prop :=
  l_bihomogen : forall (a : A) (x : B) (y : C),
    a * bin_fn x y = bin_fn (a * x) y.
