(* bad *)
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.Function.
From Maniunfold.Has Require Export
  TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.UnaryDistributive TwoSorted.RightBinaryCommutative
  TwoSorted.LeftModule.
From Maniunfold.Is Require Export
  OneSorted.UnaryDistributive TwoSorted.RightBinaryCommutative
  TwoSorted.RightModule.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

(** A left linear map is a left module homomorphism. *)

(* LeftHomogeneous *)
Class IsLHomogen (A B C : Type)
  (A_B_has_l_act : HasLAct A B) (A_C_has_l_act : HasLAct A C)
  (B_C_has_fn : HasFn B C) : Prop :=
  l_homogen : forall (a : A) (x : B), fn (a L* x) = a L* fn x.

(* Additive *)
Class IsAddve (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_fn : HasFn A B) : Prop :=
  addve : forall x y : A, fn (x + y) = fn x + fn y.

(* LeftLinearMap LeftModuleHomomorphism *)
Class IsLLinMap (A B C : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_l_act : HasLAct A B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_l_act : HasLAct A C)
  (B_C_has_fn : HasFn B C) : Prop := {
  A_B_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A B add zero neg mul one add zero neg l_act;
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A C add zero neg mul one add zero neg l_act;
  A_B_C_l_act_l_act_fn_is_l_homogen :>
    IsLHomogen A B C l_act l_act fn;
  B_C_add_add_fn_is_addve :> IsAddve B C add add fn;
}.

(** Here is the other chirality. *)

(* RightHomogeneous *)
Class IsRHomogen (A B C : Type)
  (A_B_has_r_act : HasRAct A B) (A_C_has_r_act : HasRAct A C)
  (B_C_has_fn : HasFn B C) : Prop :=
  r_homogen : forall (a : A) (x : B), fn (x R* a) = fn x R* a.

(* RightLinearMap RightModuleHomomorphism *)
Class IsRLinMap (A B C : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_r_act : HasRAct A B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_r_act : HasRAct A C)
  (B_C_has_fn : HasFn B C) : Prop := {
  A_B_add_zero_neg_mur_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod A B add zero neg mul one add zero neg r_act;
  A_C_add_zero_neg_mur_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod A C add zero neg mul one add zero neg r_act;
  A_B_C_r_act_r_act_fn_is_r_homogen :>
    IsRHomogen A B C r_act r_act fn;
  B_C_add_add_fn_is_addve' :> IsAddve B C add add fn;
}.
