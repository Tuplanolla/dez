From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Unital TwoSorted.AssociativeAlgebra.

(** Noncommutative algebra over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the monoid of algebralike structures. *)

Class IsUnlAssocAlg (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (B_has_one : HasOne B)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B) : Prop := {
  B_mul_one_is_unl :> IsUnl B mul one;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_l_act_r_act_is_assoc_alg :>
    IsAssocAlg A B add zero neg mul one add zero neg mul l_act r_act;
}.
