From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation GroupIdentity.
From Maniunfold.Is Require Export
  SemigroupHomomorphism Monoid.

Import AdditiveNotations.

Class IsMonoidHomomorphism (A B : Type) {has_hom : HasHom A B}
  {A_has_eqv : HasEqv A} {A_has_opr : HasOpr A} {A_has_idn : HasIdn A}
  {B_has_eqv : HasEqv B} {B_has_opr : HasOpr B} {B_has_idn : HasIdn B} :
  Prop := {
  monoid_homomorphism_is_semigroup_homomorphism :> IsSemigroupHomomorphism A B;
  monoid_homomorphism_preserves_identity : hom 0 == 0;
  monoid_homomorphism_A_is_monoid :> IsMonoid A;
  monoid_homomorphism_B_is_monoid :> IsMonoid B;
}.
