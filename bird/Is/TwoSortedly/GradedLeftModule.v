From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation GradedBinaryOperation GradedNullaryOperation.
From Maniunfold.Is Require Export
  GradedRing AbelianGroup.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations AdditiveNotations.

(** TODO Move these once the notations are settled. *)

Class HasGrdLAct {A : Type} (P Q : A -> Type)
  {has_bin_op : HasBinOp A} : Type :=
  grd_l_act : forall i j : A, P i -> Q j -> Q (i + j).

Typeclasses Transparent HasGrdLAct.

Reserved Notation "x 'GL+' y" (at level 50, left associativity).
Reserved Notation "x 'GL*' y" (at level 40, left associativity).

Notation "x 'GL+' y" := (grd_l_act _ _ x y) : algebra_scope.
Notation "x 'GL*' y" := (grd_l_act _ _ x y) : algebra_scope.

(** TODO Dubious... *)

Class IsGrdLMod {A : Type} {P Q : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasNullOp A)
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_bin_op : forall i : A, HasBinOp (Q i))
  (Q_has_un : forall i : A, HasNullOp (Q i))
  (Q_has_un_op : forall i : A, HasUnOp (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_null_op_add_zero_neg_grd_mul_grd_one_is_grd_ring :>
    IsGrdRing (A := A) (P := P) bin_op null_op
    (* add zero neg *) _ _ _
    grd_mul grd_one;
  (* add_l_act_is_two_r_distr :> IsTwoRDistr (A := P) (B := Q) add bin_op l_act; *)
  grd_r_distr : forall (i j : A) (a b : P i) (x : Q j),
    (a + b) GL* x = a GL* x + b GL* x;
  (* mul_l_act_is_l_compat :> IsLCompat (A := P) (B := Q) mul l_act; *)
  grd_l_compat : forall (i j k : A) (a : P i) (b : P j) (x : Q k),
    rew assoc i j k in (a GL* (b GL* x)) = (a G* b) GL* x;
  bin_op_null_op_un_op_is_ab_grp :> forall i : A,
    IsAbGrp (A := Q i) bin_op null_op un_op;
  (* bin_op_l_act_is_two_l_distr :> IsTwoLDistr (A := P) (B := Q) bin_op l_act; *)
  grd_l_distr : forall (i j : A) (a : P i) (x y : Q j),
    a GL* (x + y) = a GL* x + a GL* y;
  (* null_op_l_act_is_two_l_unl :> IsTwoLUnl (A := P) (B := Q) null_op l_act; *)
  grd_l_unl : forall (i : A) (x : Q i),
    rew l_unl i in (G1 GL* x) = x;
}.

Section Context.

Context {A : Type} {P Q : A -> Type} `{is_grd_l_mod : IsGrdLMod A P Q}.

End Context.
