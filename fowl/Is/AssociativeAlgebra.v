From DEZ.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action.
From DEZ.Is Require Export
  Associative TwoSortedAlgebra.

(** Noncommutative nonunital algebra over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the semigroup of algebralike structures. *)

Class IsAssocAlg (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B)
  `(HasActL A B) `(HasActR A B) : Prop := {
  B_mul_is_assoc :> IsAssoc (mul (A := B));
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_act_l_act_r_is_alg :>
    IsAlg add zero neg mul one add zero neg mul
    (act_l (A := A) (B := B)) (act_r (A := A) (B := B));
}.
