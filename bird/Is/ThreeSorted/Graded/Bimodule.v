(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation OneSorted.Multiplication
  OneSorted.One TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  TwoSorted.Graded.LeftModule TwoSorted.Graded.RightModule
  ThreeSorted.Bicompatible.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations
  TwoSorted.Graded.MultiplicativeNotations.

Class IsGrdBicompat {A : Type} (P Q R : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_R_has_grd_l_act : HasGrdLAct P R)
  (Q_R_has_grd_r_act : HasGrdRAct Q R) : Prop := {
  A_bin_op_is_assoc :> IsAssoc A bin_op;
  grd_bicompat : forall {i j k : A} (a : P i) (x : R j) (b : Q k),
    rew assoc i j k in
    (a * (x * b)%grd_r_mod)%grd_l_mod = ((a * x)%grd_l_mod * b)%grd_r_mod;
}.

Class IsThreeGrdBimod {A : Type} (P Q R : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (Q_has_grd_mul : HasGrdMul Q) (Q_has_grd_one : HasGrdOne Q)
  (R_has_add : forall i : A, HasAdd (R i))
  (R_has_zero : forall i : A, HasZero (R i))
  (R_has_neg : forall i : A, HasNeg (R i))
  (P_R_has_grd_l_act : HasGrdLAct P R)
  (Q_R_has_grd_r_act : HasGrdRAct Q R) : Prop := {
  P_R_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_is_grd_l_mod :>
    IsGrdLMod P R P_has_add P_has_zero P_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_l_act;
  Q_R_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_r_act_is_grd_r_mod :>
    IsGrdRMod Q R Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_r_act;
  P_Q_R_grd_l_act_grd_r_act_is_grd_bicompat :>
    IsGrdBicompat P Q R grd_l_act grd_r_act;
}.
