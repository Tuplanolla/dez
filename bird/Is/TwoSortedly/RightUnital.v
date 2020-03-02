From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation RightAction RightUnit.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRUnl2 {A B : Type} {has_eq_rel : HasEqRel B}
  (has_r_un : HasRUn A) (has_r_act : HasRAct A B) : Prop :=
  r_unl_2 : forall x : B, x R+ R0 == x.
