(** * Partial Equivalence *)

From DEZ.Has Require Export
  EquivalenceRelation.
From DEZ.Is Require Export
  Symmetric Transitive.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations.

Fail Fail Class IsPartEq (A : Type) (HR : HasEqRel A) : Prop := {
  is_sym :> IsSym _==_;
  is_trans :> IsTrans _==_;
}.

Notation IsPartEq := PER.
