From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Associative TwoSorted.Algebra.

(** Noncommutative nonunital algebra over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the semigroup of algebralike structures. *)

Class IsAssocAlg (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B)
  `(HasLAct A B) `(HasRAct A B) : Prop := {
  B_mul_is_assoc :> IsAssoc B mul;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_l_act_r_act_is_alg :>
    IsAlg A B add zero neg mul one add zero neg mul l_act r_act;
}.
