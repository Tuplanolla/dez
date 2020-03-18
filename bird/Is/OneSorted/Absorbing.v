From Maniunfold.Has Require Export
  OneSorted.Zero OneSorted.Multiplication.
From Maniunfold.Is Require Export
  OneSorted.LeftAbsorbing OneSorted.RightAbsorbing.

Class IsAbsorb {A : Type}
  (A_has_zero : HasZero A) (has_mul : HasMul A) : Prop := {
  zero_mul_is_l_absorb :> IsLAbsorb zero mul;
  zero_mul_is_r_absorb :> IsRAbsorb zero mul;
}.
