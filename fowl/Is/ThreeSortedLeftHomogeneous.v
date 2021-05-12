(* bad *)
From Maniunfold.Has Require Export
  TwoSortedLeftAction Function.
From Maniunfold.ShouldHave Require Import
  TwoSortedMultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLHomogen (A B C : Type)
  `(HasLAct A B) `(HasLAct A C)
  `(HasFn B C) : Prop :=
  l_homogen : forall (a : A) (x : B), fn (a * x) = a * fn x.
