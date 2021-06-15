(* bad *)
From Maniunfold.Has Require Export
  Action ThreeSortedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRBihomogen (A B C D : Type)
  `(HasActR A C) `(HasActR A D)
  `(HasBinFn B C D) : Prop :=
  r_bihomogen : forall (x : B) (y : C) (a : A),
    bin_fn x (y * a) = bin_fn x y * a.
