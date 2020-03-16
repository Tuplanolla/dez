From Maniunfold.Has Require Export
  EquivalenceRelation LeftAction LeftTorsion.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLNullOpiq {A B : Type}
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop :=
  l_null_opiq : forall x y : B, (y L- x) L+ x = y.
