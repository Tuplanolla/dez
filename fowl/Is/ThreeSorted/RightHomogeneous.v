(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.RightAction Function.
From Maniunfold.ShouldHave Require Import
  TwoSorted.MultiplicativeNotations.

Local Open Scope r_mod_scope.

Class IsRHomogen (A B C : Type)
  `(HasRAct A B) `(HasRAct A C)
  `(HasFn B C) : Prop :=
  r_homogen : forall (a : A) (x : B), fn (x * a) = fn x * a.
