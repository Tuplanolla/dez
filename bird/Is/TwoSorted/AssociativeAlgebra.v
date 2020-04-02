(* good *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Associative TwoSorted.Algebra.

(** This is a noncommutative nonunital algebra
    over a noncommutative ring, making it the semigroup of algebralikes.
    The ring is carried by [A] and the algebra by [B]. *)

Class IsAssocAlg (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B) : Prop := {
  mul_is_assoc :> IsAssoc (A := B) mul;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_l_act_r_act_is_alg :>
    IsAlg A B add zero neg mul one add zero neg mul l_act r_act;
}.
