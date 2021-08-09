From DEZ.Has Require Export
  Homomorphism EquivalenceRelation.
From DEZ.Is Require Export
  Proper Setoid.

Class IsSetoidHomomorphism {A B : Type}
  {A_has_eqv : HasEqv A} {B_has_eqv : HasEqv B}
  (has_hom : HasHom A B) : Prop := {
  hom_is_proper :> IsProper (eqv ==> eqv) hom;
  A_eqv_is_setoid :> IsSetoid (A := A) eqv;
  B_eqv_is_setoid :> IsSetoid (A := B) eqv;
}.
