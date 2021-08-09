From DEZ.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation GroupIdentity.
From DEZ.Is Require Export
  SemigroupHomomorphism Monoid.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

Class IsMonoidHomomorphism {A B : Type} {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) {B_has_eqv : HasEqv B}
  (B_has_opr : HasOpr B) (B_has_idn : HasIdn B)
  (has_hom : HasHom A B) : Prop := {
  A_B_opr_opr_hom_is_semigroup_homomorphism :>
    IsSemigroupHomomorphism (A := A) (B := B) opr opr hom;
  preserves_identity : hom 0 == 0;
  A_opr_idn_is_monoid :> IsMonoid (A := A) opr idn;
  B_opr_idn_is_monoid :> IsMonoid (A := B) opr idn;
}.
