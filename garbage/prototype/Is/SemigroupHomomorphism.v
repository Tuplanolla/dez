From DEZ.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation.
From DEZ.Is Require Export
  SetoidHomomorphism Semigroup.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

(** TODO Rename [preserves_operation] and the like. *)

Class IsSemigroupHomomorphism {A B : Type} {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) {B_has_eqv : HasEqv B}
  (B_has_opr : HasOpr B) (has_hom : HasHom A B) : Prop := {
  A_B_hom_is_setoid_homomorphism :>
    IsSetoidHomomorphism (A := A) (B := B) hom;
  preserves_operation : forall x y : A,
    hom (x + y) == hom x + hom y;
  A_opr_is_semigroup :> IsSemigroup (A := A) opr;
  B_opr_is_semigroup :> IsSemigroup (A := B) opr;
}.
