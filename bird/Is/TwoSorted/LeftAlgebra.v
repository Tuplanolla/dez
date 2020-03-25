From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.LeftBilinear.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations ArithmeticNotations.

(** This is a unital associative left algebra over a commutative ring. *)

Class IsLAlg {A B : Type}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (B_has_one : HasOne B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_zero_neg_mul_one_is_comm_ring :>
    IsCommRing (A := B) add zero neg mul one;
  add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := B) add zero neg mul one add zero neg l_act;
  add_add_l_act_is_l_bilin :> IsLBilin add add l_act;
}.

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
