From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Setoid Monoid Commutative.

Class IsCommutativeMonoid (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  opr_is_monoid :> IsMonoid A;
  opr_is_commutative :> IsCommutative A;
}.
