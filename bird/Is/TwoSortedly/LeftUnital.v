From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation LeftAction LeftUnit.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLUnl2 {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_un : HasLUn A) (has_l_act : HasLAct A B) : Prop :=
  l_unl_2 : forall x : B, L0 L+ x == x.
