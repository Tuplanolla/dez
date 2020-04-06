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

(** TODO Check ungraded argument order to be consistent. *)

Class IsTwoGrdRLDistr {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop :=
  grd_two_r_l_distr : forall {i j : A} (x : Q i) (a b : P j),
    x GR* (a + b) = x GR* a + x GR* b.

Class IsGrdRCompat {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_mul : HasGrdMul P)
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  grd_r_compat : forall {i j k : A} (x : Q i) (a : P j) (b : P k),
    rew assoc i j k in (x GR* (a G* b)) = (x GR* a) GR* b;
}.

Class IsTwoGrdRUnl {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_one : HasGrdOne P)
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  bin_op_null_op_is_r_unl :> IsRUnl bin_op null_op;
  grd_two_r_unl : forall {i : A} (x : Q i),
    rew r_unl i in (x GR* G1) = x;
}.

Class IsTwoGrdRRDistr {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop :=
  grd_two_r_r_distr : forall {i j : A} (x y : Q i) (a : P j),
    (x + y) GR* a = x GR* a + y GR* a.

Class IsGrdRMod {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  add_zero_neg_mul_one_is_grd_ring :>
    IsGrdRing (P := P) P_has_add P_has_zero P_has_neg grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (A := Q i) (Q_has_add i) (Q_has_zero i) (Q_has_neg i);
  add_add_grd_r_act_is_grd_two_r_distr :>
    IsTwoGrdRLDistr P Q P_has_add Q_has_add grd_r_act;
  P_Q_grd_mul_grd_r_act_is_grd_r_compat :> IsGrdRCompat P Q grd_mul grd_r_act;
  P_Q_zero_grd_r_act_is_grd_two_r_unl :> IsTwoGrdRUnl P Q grd_one grd_r_act;
  P_Q_add_grd_r_act_is_grd_two_r_distr :>
    IsTwoGrdRRDistr P Q Q_has_add grd_r_act;
}.
