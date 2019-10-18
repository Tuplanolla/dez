From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsRightIdentifiable {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) : Prop := {
  right_identifiable_eqv_is_setoid :> IsSetoid eqv;
  right_identifiable : forall x : A, x + 0 == x;
}.
