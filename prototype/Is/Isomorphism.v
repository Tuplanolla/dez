From Maniunfold.Has Require Export
  EquivalenceRelation Homomorphism.
From Maniunfold.ShouldHave Require Export
  EquivalenceNotations.
From Maniunfold.Is Require Import
  Proper Setoid.

(** TODO This overloading of [hom] is probably stupid. *)

Class IsIsomorphism {A B : Type} {A_has_eqv : HasEqv A} {B_has_eqv : HasEqv B}
  (A_B_has_hom : HasHom A B) (B_A_has_hom : HasHom B A) : Prop := {
  A_eqv_is_setoid :> IsSetoid (A := A) eqv;
  B_eqv_is_setoid :> IsSetoid (A := B) eqv;
  A_B_hom_is_proper :> IsProper (eqv ==> eqv) (hom (A := A) (B := B));
  B_A_hom_is_proper :> IsProper (eqv ==> eqv) (hom (A := B) (B := A));
  A_preserving : forall x : A, hom (hom x) == x;
  B_preserving : forall y : B, hom (hom y) == y;
}.
