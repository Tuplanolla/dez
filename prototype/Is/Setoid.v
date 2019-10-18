(** TODO Remove this after getting rid of [Add] commands. *)

From Coq Require Export
  Setoid.

From Coq Require Import
  RelationClasses.
From Maniunfold Require Export
  Init.
From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Reflexive Symmetric Transitive.

Class IsSetoid {A : Type} (has_eqv : HasEqv A) : Prop := {
  setoid_is_reflexive :> IsReflexive eqv;
  setoid_is_symmetric :> IsSymmetric eqv;
  setoid_is_transitive :> IsTransitive eqv;
}.

Section Context.

Context {A : Type} `{is_setoid : IsSetoid A}.

Global Instance setoid_is_equivalence : Equivalence eqv := {}.

End Context.
