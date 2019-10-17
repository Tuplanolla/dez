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

Class IsSetoid {A : Type} (has_eqv : HasEqv A) : Prop := {
  setoid_is_reflexive :> IsReflexive eqv;
  setoid_is_symmetric :> IsSymmetric eqv;
  setoid_is_transitive :> IsTransitive eqv;
}.

Add Parametric Relation {A : Type} `{is_setoid : IsSetoid A} : A eqv
  reflexivity proved by setoid_is_reflexive
  symmetry proved by setoid_is_symmetric
  transitivity proved by setoid_is_transitive
  as setoid_relation.
