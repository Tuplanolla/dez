(* bad *)
From DEZ.Has Require Export
  Addition Zero Negation Multiplication
  One Action.
From DEZ.Is Require Export
  TwoSortedLeftModule TwoSortedRightModule ThreeSortedBicompatible.

(** This is a bimodule.
    The underlying rings are carried by [A] and [B] and
    the bimodule itself by [C]. *)

Class IsThreeBimod (A B C : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B) `(HasOne B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasActL A C) `(HasActR B C) : Prop := {
  A_C_add_zero_neg_mul_one_add_zero_neg_act_l_is_l_mod :>
    IsLMod add zero neg mul one add zero neg (act_l (A := A) (B := C));
  B_C_add_zero_neg_mul_one_add_zero_neg_act_r_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (act_r (A := B) (B := C));
  A_B_C_act_l_act_r_is_bicompat :> IsBicompat act_l act_r;
}.
