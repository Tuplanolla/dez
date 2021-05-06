(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.LeftAction Function.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope l_mod_scope.

Class IsLHomogen (A B C : Type)
  `(HasLAct A B) `(HasLAct A C)
  `(HasFn B C) : Prop :=
  l_homogen : forall (a : A) (x : B), fn (a * x) = a * fn x.
