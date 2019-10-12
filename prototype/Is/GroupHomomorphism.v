From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  Group.
From Maniunfold.Is Require Import
  Involutive Antidistributive.

Import AdditiveNotations.

(** TODO Implement "smaller" homs first. *)

Class IsGroupHomomorphism {A B : Type} (f : A -> B)
  {A_has_eqv : HasEqv A} {A_has_opr : HasOpr A}
  {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {B_has_eqv : HasEqv B} {B_has_opr : HasOpr B}
  {B_has_idn : HasIdn B} {B_has_inv : HasInv B} : Prop := {
  morphism_proper : f ::> eqv ==> eqv;
  source_is_group :> IsGroup A;
  target_is_group :> IsGroup B;
  morphism_preserves_operation : forall x y : A, f (x + y) == f x + f y;
}.

Add Parametric Morphism {A B : Type} {f : A -> B}
  `{is_group_homomorphism : IsGroupHomomorphism A B f} : f
  with signature eqv ==> eqv
  as eqv_f_morphism.
Proof. intros x y p. apply morphism_proper; auto. Qed.

Theorem morphism_preserves_identity : forall {A B : Type}
  (f : A -> B) `{is_group_homomorphism : IsGroupHomomorphism A B f},
  f 0 == 0.
Proof.
  intros A B f ? ? ? ? ? ? ? ? ?.
  (** TODO These hints are necessary if the groups are
      not declared as coercion or instance fields. *)
  (* pose proof morphism_proper as f_proper.
  pose proof source_is_group as A_is_group.
  pose proof target_is_group as B_is_group. *)
  apply (opr_left_injective (f 0) 0 (f 0)).
  rewrite <- (morphism_preserves_operation 0 0).
  rewrite (opr_right_identifiable 0).
  rewrite (opr_right_identifiable (f 0)).
  reflexivity. Qed.

Theorem morphism_preserves_inverse : forall {A B : Type}
  (f : A -> B) `{is_group_homomorphism : IsGroupHomomorphism A B f},
  forall x : A, f (- x) == - f x.
Proof.
  intros A B f ? ? ? ? ? ? ? ? ? x.
  apply (opr_left_injective _ _ (f x)).
  rewrite <- (morphism_preserves_operation).
  rewrite (opr_right_invertible x).
  rewrite (opr_right_invertible (f x)).
  rewrite (morphism_preserves_identity f).
  reflexivity. Qed.
