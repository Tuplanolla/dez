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
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B) `(HasOne B)
  `(HasLAct A B) `(HasRAct A B) : Prop := {
  B_mul_one_is_unl :> IsUnl mul one;
  A_B_add_zero_neg_mul_one_add_zero_neg_mul_l_act_r_act_is_assoc_alg :>
    IsAssocAlg add zero neg mul one add zero neg mul
    (l_act (A := A) (B := B)) (r_act (A := A) (B := B));
}.
