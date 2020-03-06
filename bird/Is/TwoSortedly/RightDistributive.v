From Maniunfold.Has Require Export
  EquivalenceRelation Addition LeftAction.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations ArithmeticNotations.

Class IsTwoRDistr {A B : Type} {has_eq_rel : HasEqRel B}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (has_l_act : HasLAct A B) : Prop :=
  two_r_distr : forall (a b : A) (x : B), (a + b) L* x == a L* x + b L* x.
