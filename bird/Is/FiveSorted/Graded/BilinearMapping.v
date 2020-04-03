(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One
  ThreeSorted.Graded.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  TwoSorted.Graded.LeftModule TwoSorted.Graded.RightModule
  ThreeSorted.Graded.Bimodule
  TwoSorted.Graded.Bimodule
  TwoSorted.Unital TwoSorted.Isomorphism.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations
  OneSorted.Graded.ArithmeticNotations
  TwoSorted.Graded.MultiplicativeNotations.

(** This does not work yet, but we are getting there. *)

(** TODO Relocate this crap. *)

(* LeftBihomogeneous *)
Class IsGrdLBihomogen (A B C D : Type)
  (A_B_has_l_act : HasLAct A B) (A_D_has_l_act : HasLAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  grd_l_bihomogen : forall (a : A) (x : B) (y : C),
    bin_fn (a L* x) y = a L* bin_fn x y.

(* RightBihomogeneous *)
Class IsGrdRBihomogen (A B C D : Type)
  (A_C_has_r_act : HasRAct A C) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  grd_r_bihomogen : forall (x : B) (y : C) (a : A),
    bin_fn x (y R* a) = bin_fn x y R* a.

(* Bihomogeneous *)
Class IsGrdBihomogen {A : Type} (P Q R S T : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_R_has_grd_l_act : HasGrdLAct P R)
  (Q_S_has_grd_r_act : HasGrdRAct Q S)
  (P_T_has_grd_l_act : HasGrdLAct P T)
  (Q_T_has_grd_r_act : HasGrdRAct Q T)
  (R_S_T_has_grd_bin_fn : HasGrdBinFn R S T) : Prop := {
  (*
  P_R_S_T_grd_l_act_grd_l_act_grd_bin_fn_is_grd_l_bihomogen :>
    IsGrdLBihomogen P R S T grd_l_act grd_l_act grd_bin_fn;
  Q_R_S_T_grd_r_act_grd_r_act_grd_bin_fn_is_grd_r_bihomogen :>
    IsGrdRBihomogen Q R S T grd_r_act grd_r_act grd_bin_fn;
  *)
}.

(* LeftBiadditive *)
Class IsGrdLBiaddve (A B C : Type)
  (A_has_add : HasAdd A) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  grd_l_biaddve : forall (x y : A) (z : B),
    bin_fn (x + y) z = bin_fn x z + bin_fn y z.

(* RightBiadditive *)
Class IsGrdRBiaddve (A B C : Type)
  (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  grd_r_biaddve : forall (x : A) (y z : B),
    bin_fn x (y + z) = bin_fn x y + bin_fn x z.

(* Biadditive *)
Class IsGrdBiaddve {A : Type} (P Q R : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (Q_has_add : forall i : A, HasAdd (Q i))
  (R_has_add : forall i : A, HasAdd (R i))
  (P_Q_R_has_grd_bin_fn : HasGrdBinFn P Q R) : Prop := {
  (*
  P_Q_R_add_add_grd_bin_fn_is_grd_l_biaddve :>
    IsGrdLBiaddve P Q R add add grd_bin_fn;
  P_Q_R_add_add_grd_bin_fn_is_grd_r_biaddve :>
    IsGrdRBiaddve P Q R add add grd_bin_fn;
  *)
}.

(** This is a graded bilinear mapping from two modules into a bimodule,
    each of them defined over a noncommutative ring.
    The rings are carried by [A] and [B], the modules by [C] and [D] and
    the bimodule by [E].
    The mapping itself is an arbitrary binary function. *)

Class IsGrdBilinMap {A : Type} (P Q R S T : A -> Type)
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
  (S_has_add : forall i : A, HasAdd (S i))
  (S_has_zero : forall i : A, HasZero (S i))
  (S_has_neg : forall i : A, HasNeg (S i))
  (T_has_add : forall i : A, HasAdd (T i))
  (T_has_zero : forall i : A, HasZero (T i))
  (T_has_neg : forall i : A, HasNeg (T i))
  (R_S_T_has_grd_bin_fn : HasGrdBinFn R S T)
  (P_R_has_grd_l_act : HasGrdLAct P R)
  (Q_S_has_grd_r_act : HasGrdRAct Q S)
  (P_T_has_grd_l_act : HasGrdLAct P T)
  (Q_T_has_grd_r_act : HasGrdRAct Q T) : Prop := {
  P_R_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_is_grd_l_mod :>
    IsGrdLMod P R P_has_add P_has_zero P_has_neg grd_mul grd_one
    R_has_add R_has_zero R_has_neg grd_l_act;
  Q_S_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_r_act_is_grd_r_mod :>
    IsGrdRMod Q S Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    S_has_add S_has_zero S_has_neg grd_r_act;
  P_Q_T_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_grd_r_act_is_three_grd_bimod
    :> IsThreeGrdBimod P Q T
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg grd_mul grd_one
    T_has_add T_has_zero T_has_neg grd_l_act grd_r_act;
  P_Q_R_S_T_grd_l_act_grd_r_act_grd_l_act_grd_r_act_grd_bin_fn_is_grd_bihomogen
    :> IsGrdBihomogen P Q R S T
    grd_l_act grd_r_act grd_l_act grd_r_act grd_bin_fn;
  R_S_T_add_add_add_grd_bin_fn_is_grd_biaddve :>
    IsGrdBiaddve R S T R_has_add S_has_add T_has_add grd_bin_fn;
}.

(** TODO Relocate this too. *)

(** This is a graded bilinear operator.
    The scalars are carried by [A] and the vectors by [B].
    We adopt the convention that the operator itself is multiplicative. *)

Class IsGrdBilinOp {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (Q_has_grd_mul : HasGrdMul Q)
  (P_Q_has_grd_l_act : HasGrdLAct P Q)
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop :=
  P_P_Q_Q_Q_P_has_add_P_has_zero_P_has_neg_grd_mul_grd_one_P_has_add_P_has_zero_P_has_neg_grd_mul_grd_one_Q_has_add_Q_has_zero_Q_has_neg_Q_has_add_Q_has_zero_Q_has_neg_Q_has_add_Q_has_zero_Q_has_neg_grd_mul_grd_l_act_grd_r_act_grd_l_act_grd_r_act_is_bilin_map
    :> IsGrdBilinMap P P Q Q Q
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg
    Q_has_add Q_has_zero Q_has_neg
    Q_has_add Q_has_zero Q_has_neg grd_mul
    grd_l_act grd_r_act grd_l_act grd_r_act.
