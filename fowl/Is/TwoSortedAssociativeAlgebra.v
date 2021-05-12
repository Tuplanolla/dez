From Maniunfold.Has Require Export
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  TwoSortedLeftAction TwoSortedRightAction.
From Maniunfold.Is Require Export
  OneSortedAssociative TwoSortedAlgebra.

(** Noncommutative nonunital algebra over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the semigroup of algebralike structures. *)

Class IsAssocAlg (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B)
  `(HasLAct A B) `(HasRAct A B) : Prop := {
  B_mul_is_assoc :> IsAssoc (mul (A := B));
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_l_act_r_act_is_alg :>
    IsAlg add zero neg mul one add zero neg mul
    (l_act (A := A) (B := B)) (r_act (A := A) (B := B));
}.
