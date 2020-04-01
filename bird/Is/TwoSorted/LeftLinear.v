From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.Function.
From Maniunfold.Is Require Export
  OneSorted.UnaryDistributive TwoSorted.RightBinaryCommutative
  TwoSorted.LeftModule.
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