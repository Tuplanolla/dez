(* bad *)
From Maniunfold.Has Require Export
  Action.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRHomogen (A B C : Type)
  `(HasActR A B) `(HasActR A C)
  (f : B -> C) : Prop :=
  r_homogen : forall (a : A) (x : B), f (x * a) = f x * a.
