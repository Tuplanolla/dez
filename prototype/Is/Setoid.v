From Coq Require Import Basics Setoid Morphisms.
From Maniunfold.Has Require Import EquivalenceRelation.
From Maniunfold.Is Require Import Reflexive Symmetric Transitive.

(** We need to perform this song and dance
    to be compatible with the standard library setoid. *)
Export Basics Setoid Morphisms.

Module Export ProperNotations.

Export Morphisms.ProperNotations.

Open Scope signature_scope.

Reserved Notation "R '==>' S" (at level 55, right associativity).
(* Notation "R '==>' S" := (respectful R S) : signature_scope. *)

Reserved Notation "x '::>' R" (at level 70, no associativity).
Notation "x '::>' R" := (Proper R x) : signature_scope.

End ProperNotations.

(** We do not use the standard library setoid directly, because
    - it is not a predicative class in [Prop] and
    - it is not constrained by an operational class like [Eqv]. *)
Class IsSetoid (A : Type) {has_eqv : HasEqv A} : Prop := {
  eqv_is_reflexive :> IsReflexive A;
  eqv_is_symmetric :> IsSymmetric A;
  eqv_is_transitive :> IsTransitive A;
}.

Add Parametric Relation {A : Type} `{is_setoid : IsSetoid A} : A eqv
  reflexivity proved by eqv_is_reflexive
  symmetry proved by eqv_is_symmetric
  transitivity proved by eqv_is_transitive
  as eqv_relation.
