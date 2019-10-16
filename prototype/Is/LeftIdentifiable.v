From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsLeftIdentifiable (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  left_identifiable_is_setoid :> IsSetoid A;
  left_identifiable : forall x : A, 0 + x == x;
}.
