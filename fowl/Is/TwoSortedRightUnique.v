(* bad *)
From DEZ.Has Require Export
  Action Torsion.
From DEZ.Supports Require Import
  TwoSortedAdditiveNotations.

Local Open Scope r_mod_scope.

Class IsRUniq (A B : Type)
  `(HasActR A B) `(HasTorR A B) : Prop :=
  r_uniq : forall x y : B, x + (y - x)%r_subgrp = y.
