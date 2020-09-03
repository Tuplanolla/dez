From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  FiveSorted.BilinearMapping.

(** Bilinear operator on a bimodule over a noncommutative ring.
    The scalars are carried by [A] and the vectors by [B].
    We refer to the operator as multiplication,
    so that it does not get mixed up with addition,
    since they both have the same type and same superclasses. *)

Class IsBilinOp (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B)
  (B_has_mul : HasMul B) : Prop :=
  A_A_B_B_B_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_add_zero_neg_add_zero_neg_l_act_r_act_l_act_r_act_mul_is_bilin_map
    :> IsBilinMap A A B B B add zero neg mul one add zero neg mul one
    add zero neg add zero neg add zero neg l_act r_act l_act r_act mul.