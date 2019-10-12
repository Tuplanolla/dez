From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  SetoidHomomorphism Semigroup.

Import AdditiveNotations.

Class IsSemigroupHomomorphism (A B : Type) {has_hom : HasHom A B}
  {A_has_eqv : HasEqv A} {A_has_opr : HasOpr A}
  {B_has_eqv : HasEqv B} {B_has_opr : HasOpr B} : Prop := {
  hom_is_setoid_homomorphism :> IsSetoidHomomorphism A B;
  hom_preserves_operation : forall x y : A, hom (x + y) == hom x + hom y;
  A_is_semigroup :> IsSemigroup A;
  B_is_semigroup :> IsSemigroup B;
}.
