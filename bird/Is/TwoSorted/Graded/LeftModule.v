(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  Graded.BinaryOperation Graded.NullaryOperation TwoSorted.Graded.LeftAction.
From Maniunfold.Is Require Export
  Graded.Ring AbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations
  TwoSorted.Graded.MultiplicativeNotations.

(** TODO Relocate these classes. *)

Class IsTwoGrdLRDistr {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop :=
  grd_two_l_r_distr : forall {i j : A} (a b : P i) (x : Q j),
    (a + b) GL* x = a GL* x + b GL* x.

Class IsGrdLCompat {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_mul : HasGrdMul P)
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  grd_l_compat : forall {i j k : A} (a : P i) (b : P j) (x : Q k),
    rew assoc i j k in (a GL* (b GL* x)) = (a G* b) GL* x;
}.

Class IsTwoGrdLUnl {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_one : HasGrdOne P)
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  grd_two_l_unl : forall {i : A} (x : Q i),
    rew l_unl i in (G1 GL* x) = x;
}.

Class IsTwoGrdLLDistr {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop :=
  grd_two_l_l_distr : forall {i j : A} (a : P i) (x y : Q j),
    a GL* (x + y) = a GL* x + a GL* y.

Class IsGrdLMod {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing (P := P) P_has_add P_has_zero P_has_neg grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (A := Q i) (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  P_Q_add_add_grd_l_act_is_grd_two_r_distr :>
    IsTwoGrdLRDistr P Q P_has_add Q_has_add grd_l_act;
  P_Q_grd_mul_grd_l_act_is_grd_l_compat :> IsGrdLCompat P Q grd_mul grd_l_act;
  P_Q_zero_grd_l_act_is_grd_two_l_unl :> IsTwoGrdLUnl P Q grd_one grd_l_act;
  P_Q_add_grd_l_act_is_grd_two_l_distr :>
    IsTwoGrdLLDistr P Q Q_has_add grd_l_act;
}.
