From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation.
From Maniunfold.Is Require Export
  Proper Setoid.

Class IsSetoidHomomorphism {A B : Type}
  {A_has_eqv : HasEqv A} {B_has_eqv : HasEqv B}
  (has_hom : HasHom A B) : Prop := {
  setoid_homomorphism_is_proper :> IsProper (eqv ==> eqv) hom;
  setoid_homomorphism_A_is_setoid :> IsSetoid (A := A) eqv;
  setoid_homomorphism_B_is_setoid :> IsSetoid (A := B) eqv;
}.
