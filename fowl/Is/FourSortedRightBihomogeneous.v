(* bad *)
From Maniunfold.Has Require Export
  TwoSortedRightAction ThreeSortedBinaryFunction.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRBihomogen (A B C D : Type)
  `(HasRAct A C) `(HasRAct A D)
  `(HasBinFn B C D) : Prop :=
  r_bihomogen : forall (x : B) (y : C) (a : A),
    bin_fn x (y * a) = bin_fn x y * a.
