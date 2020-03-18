From Maniunfold.Has Require Export
  EquivalenceRelation Join Meet.
From Maniunfold.ShouldHave Require Import
  LatticeNotations.

Class IsSorb {A : Type}
  (has_join : HasJoin A) (has_meet : HasMeet A) : Prop :=
  l_sorb : forall x y : A, (x \/ (x /\ y)) = x.
