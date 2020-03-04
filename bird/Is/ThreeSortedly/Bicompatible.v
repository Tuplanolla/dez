From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation LeftAction RightAction.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsBicompat {A B C : Type} {has_eq_rel : HasEqRel C}
  (has_l_act : HasLAct A C) (has_r_act : HasRAct B C) : Prop :=
  bicompat : forall (x : A) (y : C) (z : B), x L+ (y R+ z) == (x L+ y) R+ z.