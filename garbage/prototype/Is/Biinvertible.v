From DEZ.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From DEZ.Is Require Export
  LeftInvertible RightInvertible.

Class IsBiinvertible {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) (has_inv : HasInv A) : Prop := {
  opr_idn_inv_is_left_invertible :> IsLeftInvertible opr idn inv;
  opr_idn_inv_is_right_invertible :> IsRightInvertible opr idn inv;
}.
