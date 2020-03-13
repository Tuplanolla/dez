From Maniunfold.Has Require Export
  EquivalenceRelation Addition LeftAction.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations ArithmeticNotations.

Class IsTwoLDistr {A B : Type}
  (has_add : HasAdd B) (has_l_act : HasLAct A B) : Prop :=
  two_l_distr : forall (a : A) (x y : B), a L* (x + y) = a L* x + a L* y.
