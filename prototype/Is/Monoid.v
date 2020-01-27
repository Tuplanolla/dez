From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Semigroup Biidentifiable.

Class IsMonoid {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  opr_is_semigroup :> IsSemigroup opr;
  opr_idn_is_identifiable :> IsBiidentifiable opr idn;
}.
