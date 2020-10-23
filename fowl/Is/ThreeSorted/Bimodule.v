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
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B) `(HasOne B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasLAct A C) `(HasRAct B C) : Prop := {
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod add zero neg mul one add zero neg (l_act (A := A) (B := C));
  B_C_add_zero_neg_mul_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (r_act (A := B) (B := C));
  A_B_C_l_act_r_act_is_bicompat :> IsBicompat l_act r_act;
}.
