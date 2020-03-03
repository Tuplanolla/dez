From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation LeftAction LeftUnit.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsTwoLUnl {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_un : HasLUn A) (has_l_act : HasLAct A B) : Prop :=
  two_l_unl : forall x : B, L0 L+ x == x.
