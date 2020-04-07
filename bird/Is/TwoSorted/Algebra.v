From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Ring TwoSorted.Bimodule TwoSorted.BilinearOperator.

(** Noncommutative nonunital nonassociative algebra
    over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the magma of algebralike structures. *)

Class IsAlg (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B) : Prop := {
  add_zero_neg_mul_one_is_ring :> IsRing (A := A) add zero neg mul one;
  A_B_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_two_bimod :>
    IsTwoBimod A B add zero neg mul one add zero neg l_act r_act;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_l_act_r_act_is_bilin_op :>
    IsBilinOp A B add zero neg mul one add zero neg l_act r_act mul;
}.
