(** * Partial Equivalence *)

From Coq Require Import
  Classes.RelationClasses.
From DEZ.Is Require Export
  Symmetric Transitive.

(** ** Partial Equivalence Relation *)

Fail Fail Class IsPartEquiv (A : Type) (X : A -> A -> Prop) : Prop := {
  part_equiv_is_sym :> IsSym X;
  part_equiv_is_trans :> IsTrans X;
}.

Arguments RelationClasses.PER {_} _.
Arguments RelationClasses.PER_Symmetric {_ _ _} _ _ _.
Arguments RelationClasses.PER_Transitive {_ _ _} _ _ _ _ _.

Notation IsPartEquiv := RelationClasses.PER.
Notation part_equiv_is_sym := RelationClasses.PER_Symmetric.
Notation part_equiv_is_trans := RelationClasses.PER_Transitive.
