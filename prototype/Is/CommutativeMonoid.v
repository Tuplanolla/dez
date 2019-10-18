From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Setoid Monoid Commutative.

Class IsCommutativeMonoid {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  commutative_monoid_opr_idn_is_monoid :> IsMonoid opr idn;
  commutative_monoid_opr_is_commutative :> IsCommutative opr;
}.
