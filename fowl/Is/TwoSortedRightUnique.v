(* bad *)
From Maniunfold.Has Require Export
  Action TwoSortedRightTorsion.
From Maniunfold.ShouldHave Require Import
  TwoSortedAdditiveNotations.

Local Open Scope r_mod_scope.

Class IsRUniq (A B : Type)
  `(HasActR A B) `(HasRTor A B) : Prop :=
  r_uniq : forall x y : B, x + (y - x)%r_subgrp = y.
