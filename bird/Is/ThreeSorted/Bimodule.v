(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation OneSorted.Multiplication
  OneSorted.One TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  TwoSorted.LeftModule TwoSorted.RightModule ThreeSorted.Bicompatible.

(** This is a bimodule.
    The underlying rings are carried by [A] and [B] and
    the bimodule itself by [C]. *)

Class IsThreeBimod (A B C : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (B_has_one : HasOne B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_l_act : HasLAct A C) (B_C_has_r_act : HasRAct B C) : Prop := {
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A C add zero neg mul one add zero neg l_act;
  B_C_add_zero_neg_mul_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod B C add zero neg mul one add zero neg r_act;
  A_B_C_l_act_r_act_is_bicompat :> IsBicompat A B C l_act r_act;
}.
