From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation.
From Maniunfold.Is Require Export
  Setoid.

(** TODO The choice of implicit arguments here is dubious.
    It would probably be more sensible to replace
    [IsSetoidHomomorphism (A B : Type) {has_hom : HasHom A B}] with
    [IsSetoidHomomorphism {A B : Type} (has_hom : HasHom A B)],
    but we shall live with this choice until it bites us in the ass. *)

Class IsSetoidHomomorphism (A B : Type) {has_hom : HasHom A B}
  {A_has_eqv : HasEqv A} {B_has_eqv : HasEqv B} : Prop := {
  hom_proper :> IsProper (eqv ==> eqv) hom;
  A_is_setoid :> IsSetoid A;
  B_is_setoid :> IsSetoid B;
}.

Add Parametric Morphism {A B : Type}
  `{is_setoid_homomorphism : IsSetoidHomomorphism A B} : hom
  with signature eqv ==> eqv
  as eqv_hom_morphism.
Proof. intros x y p. apply hom_proper; auto. Qed.
