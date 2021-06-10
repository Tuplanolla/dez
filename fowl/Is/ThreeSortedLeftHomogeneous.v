(* bad *)
From Maniunfold.Has Require Export
  TwoSortedLeftAction.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLHomogen (A B C : Type)
  `(HasLAct A B) `(HasLAct A C)
  (f : B -> C) : Prop :=
  l_homogen : forall (a : A) (x : B), f (a * x) = a * f x.
