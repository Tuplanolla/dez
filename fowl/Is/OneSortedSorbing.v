(* bad *)
From Maniunfold.Has Require Export
  OneSortedEquivalenceRelation OneSortedJoin OneSortedMeet.
From Maniunfold.ShouldHave Require Import
  OneSortedLatticeNotations.

Class IsSorb (A : Type)
  `(HasJoin A) `(HasMeet A) : Prop :=
  l_sorb : forall x y : A, (x \/ (x /\ y)) = x.
