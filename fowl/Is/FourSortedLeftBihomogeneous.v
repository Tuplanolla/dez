(* bad *)
From DEZ.Has Require Export
  Action ThreeSortedBinaryFunction.
From DEZ.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLBihomogen (A B C D : Type)
  `(HasActL A B) `(HasActL A D)
  `(HasBinFn B C D) : Prop :=
  l_bihomogen : forall (a : A) (x : B) (y : C),
    a * bin_fn x y = bin_fn (a * x) y.
