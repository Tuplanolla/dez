From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.Multiplication.
From Maniunfold.Is Require Export
  OneSorted.LeftAbsorbing OneSorted.RightAbsorbing.

Class IsAbsorb (A : Type)
  (A_has_zero : HasZero A) (A_has_mul : HasMul A) : Prop := {
  A_zero_mul_is_l_absorb :> IsLAbsorb A zero mul;
  A_zero_mul_is_r_absorb :> IsRAbsorb A zero mul;
}.
