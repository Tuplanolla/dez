From Coq Require Logic. Import Logic.EqNotations.
From Maniunfold.Has Require Export
  BinaryOperation Unit GradedBinaryOperation GradedUnit.
From Maniunfold.Is Require Export
  GradedRing AbelianGroup.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations AdditiveNotations.
From Maniunfold.ShouldOffer Require Import
  MoreAdditiveNotations.

(** TODO Move these once the notations are settled. *)

Class HasGrdLAct {A : Type} (P Q : A -> Type)
  {has_bin_op : HasBinOp A} : Type :=
  grd_l_act : forall i j : A, P i -> Q j -> Q (i + j).

Typeclasses Transparent HasGrdLAct.

Reserved Notation "x 'GL+' y" (at level 50, left associativity).
Reserved Notation "x 'GL*' y" (at level 40, left associativity).

Local Notation "x 'GL+' y" := (grd_l_act _ _ x y) : algebra_scope.
Local Notation "x 'GL*' y" := (grd_l_act _ _ x y) : algebra_scope.

(** TODO Finish this definition. *)

Class IsGrdLMod {A : Type} {P Q : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasUn A) (A_has_un_op : HasUnOp A)
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_bin_op : forall i : A, HasBinOp (Q i))
  (Q_has_un : forall i : A, HasUn (Q i))
  (Q_has_un_op : forall i : A, HasUnOp (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  bin_op_un_add_zero_neg_grd_mul_grd_one_is_grd_ring :>
    IsGrdRing (A := A) (P := P) bin_op un
    (* add zero neg *) P_has_add P_has_zero P_has_neg
    grd_mul grd_one;
  (* add_l_act_is_two_r_distr :> IsTwoRDistr (A := P) (B := Q) add bin_op l_act; *)
    (* two_r_distr : forall (a b : A) (x : B), (a + b) L* x = a L* x + b L* x; *)
  (* mul_l_act_is_l_compat :> IsLCompat (A := P) (B := Q) mul l_act; *)
    (* l_compat : forall (a b : A) (x : B), (a + b) L+ x = a L+ (b L+ x); *)
  bin_op_un_un_op_is_ab_grp :> forall i : A,
    IsAbGrp (A := Q i) bin_op un un_op;
  (* bin_op_l_act_is_two_l_distr :> IsTwoLDistr (A := P) (B := Q) bin_op l_act; *)
    (* two_l_distr : forall (a : A) (x y : B), a L* (x + y) = a L* x + a L* y; *)
  (* un_l_act_is_two_l_unl :> IsTwoLUnl (A := P) (B := Q) un l_act; *)
    (* two_l_unl : forall x : B, L0 L+ x = x; *)
}.
