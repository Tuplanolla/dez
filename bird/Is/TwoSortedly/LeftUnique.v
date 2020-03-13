From Maniunfold.Has Require Export
  EquivalenceRelation LeftAction LeftTorsion.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLUniq {A B : Type} {B_has_eq_rel : HasEqRel B}
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop :=
  l_uniq : forall x y : B, (y L- x) L+ x = y.
