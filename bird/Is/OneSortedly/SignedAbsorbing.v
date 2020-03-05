From Maniunfold.Has Require Export
  EquivalenceRelation Negation Multiplication One.
From Maniunfold.Is Require Export
  LeftSignedAbsorbing RightSignedAbsorbing.

Class IsSgnAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_neg : HasNeg A) (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  neg_mul_one_is_l_sgn_absorb :> IsLSgnAbsorb neg mul one;
  neg_mul_one_is_r_sgn_absorb :> IsRSgnAbsorb neg mul one;
}.
