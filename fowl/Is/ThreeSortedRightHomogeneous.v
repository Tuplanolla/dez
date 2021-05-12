(* bad *)
From Maniunfold.Has Require Export
  TwoSortedRightAction Function.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRHomogen (A B C : Type)
  `(HasRAct A B) `(HasRAct A C)
  `(HasFn B C) : Prop :=
  r_homogen : forall (a : A) (x : B), fn (x * a) = fn x * a.
