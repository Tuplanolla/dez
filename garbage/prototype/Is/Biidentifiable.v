From DEZ.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From DEZ.Is Require Export
  LeftIdentifiable RightIdentifiable.

Class IsBiidentifiable {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  opr_idn_is_left_identifiable :> IsLeftIdentifiable opr idn;
  opr_idn_is_right_identifiable :> IsRightIdentifiable opr idn;
}.
