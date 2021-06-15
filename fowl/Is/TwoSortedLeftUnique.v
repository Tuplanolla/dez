(* bad *)
From Maniunfold.Has Require Export
  Action Torsion.
From Maniunfold.ShouldHave Require Import
  TwoSortedAdditiveNotations.

Local Open Scope l_mod_scope.

Class IsLUniq (A B : Type)
  `(HasActL A B) `(HasTorL A B) : Prop :=
  l_uniq : forall x y : B, (y - x)%l_subgrp + x = y.
