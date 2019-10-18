From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Semigroup Identifiable.

Class IsMonoid {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  monoid_opr_is_semigroup :> IsSemigroup opr;
  monoid_opr_idn_is_identifiable :> IsIdentifiable opr idn;
}.
