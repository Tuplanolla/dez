(** * Partial Equivalence *)

From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Symmetric Transitive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.

Fail Fail Class IsPartEq (A : Type) (HR : HasEqRel A) : Prop := {
  is_sym :> IsSym _==_;
  is_trans :> IsTrans _==_;
}.

Notation IsPartEq := PER.
