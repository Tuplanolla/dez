From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Import
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing TwoSorted.LeftModule.

(** TODO Check this and find a justification for the higher-sortedness. *)

Class IsLBilin {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_add_l_act_is_two_l_distr :> IsTwoLDistr add add l_act;
  add_l_act_is_bicompat :> IsBicompat add l_act;
  l_act_add_is_bicompat :> IsBicompat l_act add;
}.

(** TODO This is a more verbatim translation of literature. *)

Class IsBilinMapComm {A B C D : Type}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_l_act : HasLAct A B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_l_act : HasLAct A C)
  (D_has_add : HasAdd D) (D_has_zero : HasZero D) (D_has_neg : HasNeg D)
  (A_D_has_l_act : HasLAct A D) : Prop := {
  A_add_zero_neg_mul_one_is_comm_ring :>
    IsCommRing (A := A) add zero neg mul one;
  A_B_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := B) add zero neg mul one add zero neg l_act;
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := C) add zero neg mul one add zero neg l_act;
  A_D_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := D) add zero neg mul one add zero neg l_act;
}.

(** TODO Bilinear forms are symmetric bilinear maps, so why not say so. *)

(*
Class IsLBilin' {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_is_l_lin :> forall y : _, IsLLin add (fun x => x + y) l_act;
  flip_add_is_l_lin :> forall x : _, IsLLin add (fun y => x + y) l_act;
}.
*)

(** TODO Figure out which formulation is better.

<<
IsBilin iff
- IsLin (fun x => x + y)
- IsLin (fun y => x + y).
IsBilin iff
- IsTwoLDistr add l_act
- IsBicompat add l_act
- IsBicompat l_act add.
>> *)
