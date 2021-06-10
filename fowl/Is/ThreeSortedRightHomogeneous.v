(* bad *)
From Maniunfold.Has Require Export
  TwoSortedRightAction.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRHomogen (A B C : Type)
  `(HasRAct A B) `(HasRAct A C)
  (f : B -> C) : Prop :=
  r_homogen : forall (a : A) (x : B), f (x * a) = f x * a.
