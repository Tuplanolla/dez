From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  SetoidHomomorphism Semigroup.

Import AdditiveNotations.

Class IsSemigroupHomomorphism (A B : Type) {has_hom : HasHom A B}
  {A_has_eqv : HasEqv A} {A_has_opr : HasOpr A}
  {B_has_eqv : HasEqv B} {B_has_opr : HasOpr B} : Prop := {
  semigroup_homomorphism_is_setoid_homomorphism :> IsSetoidHomomorphism A B;
  semigroup_homomorphism_preserves_operation : forall x y : A,
    hom (x + y) == hom x + hom y;
  semigroup_homomorphism_A_is_semigroup :> IsSemigroup A;
  semigroup_homomorphism_B_is_semigroup :> IsSemigroup B;
}.
