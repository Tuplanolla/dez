From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  LeftIdentifiable RightIdentifiable.

Import AdditiveNotations.

Class IsIdentifiable {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  opr_is_left_identifiable :> IsLeftIdentifiable opr idn;
  opr_is_right_identifiable :> IsRightIdentifiable opr idn;
}.
