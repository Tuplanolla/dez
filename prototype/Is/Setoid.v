(** This module is a bit awkward,
    because it tries to be compatible with the standard library setoid. *)

From Coq Require Export
  Setoid.
From Maniunfold Require Export
  Settings.
From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Proper Reflexive Symmetric Transitive.

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
