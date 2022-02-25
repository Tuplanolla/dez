(* bad *)
From DEZ.Has Require Export
  Action.
From DEZ.Supports Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLHomogen (A B C : Type)
  `(HasActL A B) `(HasActL A C)
  (f : B -> C) : Prop :=
  l_homogen : forall (a : A) (x : B), f (a * x) = a * f x.
