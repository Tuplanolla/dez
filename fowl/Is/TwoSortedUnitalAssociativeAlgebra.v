From Maniunfold.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action.
From Maniunfold.Is Require Export
  Unital AssociativeAlgebra.

(** Noncommutative algebra over a noncommutative ring.
    The ring is carried by [A] and the algebra by [B].
    Informally, this is the monoid of algebralike structures. *)

Class IsUnlAssocAlg (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B) `(HasOne B)
  `(HasActL A B) `(HasActR A B) : Prop := {
  B_mul_one_is_unl :> IsUnl one mul;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_act_l_act_r_is_assoc_alg :>
    IsAssocAlg add zero neg mul one add zero neg mul
    (act_l (A := A) (B := B)) (act_r (A := A) (B := B));
}.
