From Maniunfold.Has Require Export
  EquivalenceRelation Join Meet.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations OrderlyNotations.

Class IsSorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_join : HasJoin A) (has_meet : HasMeet A) : Prop :=
  l_sorb : forall x y : A, x \_/ (x /^\ y) == x.
