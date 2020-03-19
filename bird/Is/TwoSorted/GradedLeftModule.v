From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  Graded.BinaryOperation Graded.NullaryOperation TwoSorted.Graded.LeftAction.
From Maniunfold.Is Require Export
  GradedRing AbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations
  TwoSorted.Graded.MultiplicativeNotations.

(** TODO Relocate these classes. *)

Class IsGrdTwoRDistr {A : Type} {P Q : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop :=
  grd_two_r_distr : forall {i j : A} (a b : P i) (x : Q j),
    (a + b) GL* x = a GL* x + b GL* x.

Class IsGrdLCompat {A : Type} {P Q : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_mul : HasGrdMul P)
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_is_assoc :> IsAssoc bin_op;
  grd_l_compat : forall {i j k : A} (a : P i) (b : P j) (x : Q k),
    rew assoc i j k in (a GL* (b GL* x)) = (a G* b) GL* x;
}.

Class IsGrdTwoLUnl {A : Type} {P Q : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_one : HasGrdOne P)
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_null_op_is_l_unl :> IsLUnl bin_op null_op;
  grd_two_l_unl : forall {i : A} (x : Q i),
    rew l_unl i in (G1 GL* x) = x;
}.

Class IsGrdTwoLDistr {A : Type} {P Q : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (Q_has_add : forall i : A, HasAdd (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop :=
  grd_two_l_distr : forall {i j : A} (a : P i) (x y : Q j),
    a GL* (x + y) = a GL* x + a GL* y.

Class IsGrdLMod {A : Type} {P Q : A -> Type}
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
  add_add_grd_l_act_is_grd_two_r_distr :>
    IsGrdTwoRDistr (P := P) (Q := Q) P_has_add Q_has_add grd_l_act;
  grd_mul_grd_l_act_is_grd_l_compat :>
    IsGrdLCompat (P := P) (Q := Q) grd_mul grd_l_act;
  zero_grd_l_act_is_grd_two_l_unl :>
    IsGrdTwoLUnl (P := P) (Q := Q) grd_one grd_l_act;
  add_grd_l_act_is_grd_two_l_distr :>
    IsGrdTwoLDistr (P := P) (Q := Q) Q_has_add grd_l_act;
}.

(** TODO Remove this context. *)

Section Context.

Context {A : Type} {P Q : A -> Type} `{is_grd_l_mod : IsGrdLMod A P Q}.

End Context.
