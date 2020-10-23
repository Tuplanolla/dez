From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.Multiplication.
From Maniunfold.Is Require Export
  OneSorted.LeftAbsorbing OneSorted.RightAbsorbing.

Class IsAbsorb (A : Type)
  `(HasZero A) `(HasMul A) : Prop := {
  A_zero_mul_is_l_absorb :> IsLAbsorb zero mul;
  A_zero_mul_is_r_absorb :> IsRAbsorb zero mul;
}.
