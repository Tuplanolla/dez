From Maniunfold.Has Require Export
  EquivalenceRelation Addition Zero Multiplication.
From Maniunfold.Is Require Export
  LeftAbsorbing RightAbsorbing.

Class IsAbsorb {A : Type} {has_eq_rel : HasEqRel A}
  (has_zero : HasZero A) (has_mul : HasMul A) : Prop := {
  zero_mul_is_l_absorb :> IsLAbsorb zero mul;
  zero_mul_is_r_absorb :> IsRAbsorb zero mul;
}.
